import OAI.LinearAlgebra.CirculantHadamard.TheoremS.Main

/-!
# Theorem S′ (sharp form)

We replace the hypothesis `p ∤ h` of Theorem S by "`p` is unramified in `ℤ[ζ_h]`", i.e.
`p ∤ h ∨ (p = 2 ∧ 4 ∤ h)`.

The point is that the values `a g` need not be `m`-th roots of unity for some `m` prime to `p`;
it suffices that they are `± ` an `m`-th root of unity with `p ∤ m`.  Indeed, `±μ_m ⊂ 𝓞(ℚ(ζ_L))`
for `L = m |H|`, and the argument of `no_perfect_prod` goes through verbatim.  When
`h = 2 h'` with `h'` odd, every `h`-th root of unity `z` satisfies `z^{h'} = ±1`, hence `z` or
`-z` is an `h'`-th root of unity, and `2 ∤ h'`.

As a corollary we get Do Duc's condition: a perfect sequence of length `n ≡ 2 (mod 4)` over the
`h`-th roots of unity forces `4 ∣ h`.
-/

namespace OAI.CirculantHadamard.TheoremS

open Finset ComplexConjugate NumberField

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Theorem S for `C_p × H`, signed-root version.**  Values `a g = ± ζ` with `ζ ^ m = 1`,
`p ∤ m`. -/
theorem no_perfect_prod_signed (H : Type*) [AddCommGroup H] [Fintype H]
    (hpH : ¬ p ∣ Fintype.card H) (m : ℕ) (hpm : ¬ p ∣ m) (a : ZMod p × H → ℂ)
    (ha : ∀ g, ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ (ε * a g) ^ m = 1)
    (hperf : ∀ s ≠ 0, ∑ g, a (g + s) * conj (a g) = 0) : False := by
  classical
  have hm0 : m ≠ 0 := by rintro rfl; exact hpm (dvd_zero p)
  set M := Fintype.card H with hMdef
  have hM0 : M ≠ 0 := Fintype.card_ne_zero
  set L := m * M with hLdef
  have : NeZero L := ⟨mul_ne_zero hm0 hM0⟩
  have hpL : ¬ p ∣ L := fun hd => (hp.out.dvd_mul.mp hd).elim hpm hpH
  obtain ⟨P, hPmax, hpP, hp2⟩ := exists_unramified_prime L p hpL
  have hPprime : P.IsPrime := hPmax.isPrime
  obtain ⟨ι, hι⟩ := exists_injective_toComplex (CyclotomicField L ℚ)
  have : IsCyclotomicExtension {L} ℚ (CyclotomicField L ℚ) :=
    CyclotomicField.isCyclotomicExtension L ℚ
  have hζ := (IsCyclotomicExtension.zeta_spec L ℚ (CyclotomicField L ℚ)).toInteger_isPrimitiveRoot
  have hζC := hζ.map_of_injective hι
  have hroot : ∀ z : ℂ, z ^ L = 1 → ∃ o, ι o = z := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := hζC.eq_pow_of_pow_eq_one hz
    exact ⟨_ ^ i, map_pow _ _ _⟩
  have hroot' : ∀ z : ℂ, z ^ L = 1 → z ∈ ι.range := fun z hz => hroot z hz
  have hsign : ∀ ε : ℂ, (ε = 1 ∨ ε = -1) → ε ∈ ι.range := by
    rintro ε (rfl | rfl)
    · exact ι.range.one_mem
    · exact ι.range.neg_mem ι.range.one_mem
  have hsq : ∀ ε : ℂ, (ε = 1 ∨ ε = -1) → ε * ε = 1 := by
    rintro ε (rfl | rfl) <;> norm_num
  have hconjε : ∀ ε : ℂ, (ε = 1 ∨ ε = -1) → conj ε = ε := by
    rintro ε (rfl | rfl) <;> simp
  -- the values and their conjugates lie in `ι.range`
  have hnorm : ∀ g, a g * conj (a g) = 1 := by
    intro g
    obtain ⟨ε, hε, hεa⟩ := ha g
    have h1 := norm_mul_conj_eq_one hm0 hεa
    rw [map_mul, hconjε ε hε] at h1
    calc a g * conj (a g) = (ε * ε) * (a g * conj (a g)) := by rw [hsq ε hε, one_mul]
      _ = 1 := by rw [← h1]; ring
  have hamem : ∀ g, a g ∈ ι.range := by
    intro g
    obtain ⟨ε, hε, hεa⟩ := ha g
    have hL : (ε * a g) ^ L = 1 := by rw [hLdef, pow_mul, hεa, one_pow]
    have : a g = ε * (ε * a g) := by rw [← mul_assoc, hsq ε hε, one_mul]
    rw [this]
    exact ι.range.mul_mem (hsign ε hε) (hroot' _ hL)
  have hcamem : ∀ g, conj (a g) ∈ ι.range := by
    intro g
    obtain ⟨ε, hε, hεa⟩ := ha g
    have hL : conj (ε * a g) ^ L = 1 := by
      rw [← map_pow, hLdef, pow_mul, hεa, one_pow, map_one]
    have : conj (a g) = ε * conj (ε * a g) := by
      rw [map_mul, hconjε ε hε, ← mul_assoc, hsq ε hε, one_mul]
    rw [this]
    exact ι.range.mul_mem (hsign ε hε) (hroot' _ hL)
  have hψL : ∀ (ψ : AddChar H ℂ) (x : H), ψ x ^ L = 1 := by
    intro ψ x
    rw [hLdef, mul_comm, pow_mul, ← AddChar.map_nsmul_eq_pow, hMdef, card_nsmul_eq_zero,
      AddChar.map_zero_eq_one, one_pow]
  have hmem : ∀ ψ y, ∃ o, ι o = fiberTransform a ψ y := fun ψ y =>
    ι.range.sum_mem fun h _ => ι.range.mul_mem (hamem _) (hroot' _ (hψL _ _))
  have hmem' : ∀ ψ y, ∃ o, ι o = conj (fiberTransform a ψ y) := by
    intro ψ y
    rw [conj_fiberTransform]
    exact ι.range.sum_mem fun h _ => ι.range.mul_mem (hcamem _) (hroot' _ (hψL _ _))
  choose x hx using hmem
  choose w hw using hmem'
  have hMnot : (M : 𝓞 (CyclotomicField L ℚ)) ∉ P :=
    natCast_notMem P hPmax.ne_top hpP ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpH)
  refine core_false P hpP M ?_ ?_ x w ?_ ?_
  · rw [Nat.cast_mul]
    exact mul_notMem_sq P hp2 hMnot
  · rw [Nat.cast_mul]
    intro hmm
    exact (hPprime.mem_or_mem hmm).elim hMnot hMnot
  · intro ψ s
    apply hι
    simp only [map_sum, map_mul, hx, hw]
    rw [fiber_corr a hnorm hperf ψ s]
    split_ifs <;> simp [hMdef]
  · apply hι
    simp only [map_sum, map_mul, hx, hw]
    rw [sum_fiber_sq a hnorm]
    simp [hMdef]

omit hp in
/-- If `p` is unramified in `ℤ[ζ_h]`, every `h`-th root of unity is `±` an `m`-th root of unity
for some `m` with `p ∤ m`. -/
lemma exists_signed_root (h p : ℕ) (hunr : ¬ p ∣ h ∨ (p = 2 ∧ ¬ 4 ∣ h)) :
    ∃ m : ℕ, ¬ p ∣ m ∧ ∀ z : ℂ, z ^ h = 1 → ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ (ε * z) ^ m = 1 := by
  have plain : ¬ p ∣ h → ∃ m : ℕ, ¬ p ∣ m ∧
      ∀ z : ℂ, z ^ h = 1 → ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ (ε * z) ^ m = 1 :=
    fun hph => ⟨h, hph, fun z hz => ⟨1, Or.inl rfl, by rw [one_mul, hz]⟩⟩
  rcases hunr with hph | ⟨rfl, h4⟩
  · exact plain hph
  · by_cases h2 : 2 ∣ h
    · obtain ⟨h', rfl⟩ := h2
      have hodd : ¬ 2 ∣ h' := by
        rintro ⟨k, rfl⟩
        exact h4 ⟨k, by ring⟩
      have hodd' : Odd h' := Nat.odd_iff.mpr (by omega)
      refine ⟨h', hodd, fun z hz => ?_⟩
      have hsq : (z ^ h') ^ 2 = 1 := by rw [← pow_mul, mul_comm, hz]
      rcases sq_eq_one_iff.mp hsq with h1 | h1
      · exact ⟨1, Or.inl rfl, by rw [one_mul, h1]⟩
      · refine ⟨-1, Or.inr rfl, ?_⟩
        rw [mul_pow, hodd'.neg_one_pow, h1]
        norm_num
    · exact plain h2

/-- **Theorem S′ (sharp form, finite abelian groups).**  If `p` is prime, `p ∣ |G|`,
`p² ∤ |G|` and `p` is unramified in `ℤ[ζ_h]` (i.e. `p ∤ h`, or `p = 2` and `4 ∤ h`), there is no
`μ_h`-valued function on `G` with perfect autocorrelation. -/
theorem no_perfect_function_sharp (G : Type*) [AddCommGroup G] [Fintype G] (h p : ℕ)
    (hp : p.Prime) (hpG : p ∣ Fintype.card G) (hp2 : ¬ p ^ 2 ∣ Fintype.card G)
    (hunr : ¬ p ∣ h ∨ (p = 2 ∧ ¬ 4 ∣ h)) (a : G → ℂ) (ha : ∀ g, a g ^ h = 1)
    (hperf : ∀ s ≠ 0, ∑ g, a (g + s) * conj (a g) = 0) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hpm, hm⟩ := exists_signed_root h p hunr
  rw [← Nat.card_eq_fintype_card] at hpG hp2
  obtain ⟨B, hB, ⟨e⟩⟩ := exists_addEquiv_zmod_prod p hpG hp2
  have : Fintype B := Fintype.ofFinite B
  rw [Nat.card_eq_fintype_card] at hB
  exact no_perfect_prod_signed B hB m hpm (fun g => a (e.symm g)) (fun g => hm _ (ha _))
    (perfect_transfer e a hperf)

/-- **Theorem S′, cyclic case (perfect sequences).**  If `p` is prime with `p ∥ n` and `p` is
unramified in `ℤ[ζ_h]`, there is no perfect sequence of length `n` over the `h`-th roots of
unity. -/
theorem no_perfect_sequence_sharp (n h p : ℕ) [NeZero n] (hp : p.Prime) (hpn : p ∣ n)
    (hp2 : ¬ p ^ 2 ∣ n) (hunr : ¬ p ∣ h ∨ (p = 2 ∧ ¬ 4 ∣ h)) (a : ZMod n → ℂ)
    (ha : ∀ x, a x ^ h = 1) (hperf : ∀ s ≠ 0, ∑ x, a (x + s) * conj (a x) = 0) : False :=
  no_perfect_function_sharp (ZMod n) h p hp (by rwa [ZMod.card]) (by rwa [ZMod.card]) hunr a ha
    hperf

/-- **Do Duc's condition (ii).**  There is no perfect sequence of length `n ≡ 2 (mod 4)` over
the `h`-th roots of unity with `h ≡ 2 (mod 4)`; i.e. `n ≡ 2 (mod 4)` forces `4 ∣ h`
(for even `h`). -/
theorem no_perfect_sequence_two_mod_four (n h : ℕ) [NeZero n] (hn : n % 4 = 2) (hh : h % 4 = 2)
    (a : ZMod n → ℂ) (ha : ∀ x, a x ^ h = 1)
    (hperf : ∀ s ≠ 0, ∑ x, a (x + s) * conj (a x) = 0) : False :=
  no_perfect_sequence_sharp n h 2 Nat.prime_two (by omega) (by norm_num; omega)
    (Or.inr ⟨rfl, by omega⟩) a ha hperf

end OAI.CirculantHadamard.TheoremS
