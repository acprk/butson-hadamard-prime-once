import OAI.LinearAlgebra.CirculantHadamard.TheoremS.Core
import OAI.LinearAlgebra.CirculantHadamard.TheoremS.Cyclotomic

/-!
# Theorem S for `G = C_p × H`

Let `p` be a prime, `H` a finite abelian group with `p ∤ |H|`, and `p ∤ h`.  There is no
`a : ZMod p × H → ℂ` with values in `μ_h` and perfect autocorrelation
`∑_g a(g + s) conj(a g) = 0` for all `s ≠ 0`.

For a character `ψ` of `H` we put `X_ψ(y) = ∑_h a(y, h) ψ(h)` (`y ∈ ZMod p`).  In `ℂ` we check
`∑_y X_ψ(y + s) conj(X_ψ(y)) = |G| [s = 0]` and `∑_ψ |X_ψ(0)|² = |H|²`.  All the numbers
`X_ψ(y)`, `conj(X_ψ(y))` are sums of `L`-th roots of unity (`L = h |H|`), so they come from
`O = 𝓞 (ℚ(ζ_L))` under an injective ring map `O → ℂ`; the identities are pulled back to `O`
and fed to `core_false` with an unramified prime `P ∣ p` of `O`.
-/

namespace OAI.CirculantHadamard.TheoremS

open Finset ComplexConjugate NumberField

variable {p : ℕ} [hp : Fact p.Prime] {H : Type*} [AddCommGroup H] [Fintype H]

/-- The fiber transform `X_ψ(y) = ∑_h a(y, h) ψ(h)`. -/
noncomputable def fiberTransform (a : ZMod p × H → ℂ) (ψ : AddChar H ℂ) (y : ZMod p) : ℂ :=
  ∑ h, a (y, h) * ψ h

omit hp in
lemma conj_fiberTransform (a : ZMod p × H → ℂ) (ψ : AddChar H ℂ) (y : ZMod p) :
    conj (fiberTransform a ψ y) = ∑ h, conj (a (y, h)) * ψ (-h) := by
  simp [fiberTransform, map_sum, AddChar.map_neg_eq_conj]

/-- Perfect autocorrelation, including the value at `0`. -/
lemma corr_eq_ite {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (a : G → ℂ)
    (hnorm : ∀ g, a g * conj (a g) = 1)
    (hperf : ∀ s ≠ 0, ∑ g, a (g + s) * conj (a g) = 0) (s : G) :
    ∑ g, a (g + s) * conj (a g) = if s = 0 then (Fintype.card G : ℂ) else 0 := by
  split_ifs with hs
  · subst hs
    simp [hnorm]
  · exact hperf s hs

/-- One fiber-transform term, expanded. -/
lemma fiber_term (a : ZMod p × H → ℂ) (ψ : AddChar H ℂ) (y s : ZMod p) :
    fiberTransform a ψ (y + s) * conj (fiberTransform a ψ y) =
      ∑ t, ψ t * ∑ h', a ((y, h') + (s, t)) * conj (a (y, h')) := by
  rw [conj_fiberTransform, fiberTransform, Finset.sum_mul_sum, Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h' _ => ?_
  refine (Fintype.sum_equiv (Equiv.addRight h') _ _ fun t => ?_).symm
  have hψ : ψ t = ψ (t + h') * ψ (-h') := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel_right]
  simp only [Equiv.coe_addRight, Prod.mk_add_mk]
  rw [hψ, add_comm h' t, add_comm y s]
  ring

/-- `X_ψ X_ψ^♯ = |G|`: the correlation of the fiber transform. -/
lemma fiber_corr [DecidableEq H] (a : ZMod p × H → ℂ) (hnorm : ∀ g, a g * conj (a g) = 1)
    (hperf : ∀ s ≠ 0, ∑ g, a (g + s) * conj (a g) = 0) (ψ : AddChar H ℂ) (s : ZMod p) :
    ∑ y, fiberTransform a ψ (y + s) * conj (fiberTransform a ψ y) =
      if s = 0 then ((p * Fintype.card H : ℕ) : ℂ) else 0 := by
  simp_rw [fiber_term]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hG : ∀ t : H, ∑ y : ZMod p, ∑ h', a ((y, h') + (s, t)) * conj (a (y, h')) =
      if ((s, t) : ZMod p × H) = 0 then ((p * Fintype.card H : ℕ) : ℂ) else 0 := by
    intro t
    rw [← Fintype.sum_prod_type' (f := fun y h' => a ((y, h') + (s, t)) * conj (a (y, h'))),
      corr_eq_ite a hnorm hperf]
    simp [Fintype.card_prod, ZMod.card]
  simp_rw [hG, Prod.mk_eq_zero, mul_ite, mul_zero]
  split_ifs with hs
  · simp [hs]
  · simp [hs]

/-- `∑_ψ |X_ψ(0)|² = |H|²`. -/
lemma sum_fiber_sq [DecidableEq H] (a : ZMod p × H → ℂ) (hnorm : ∀ g, a g * conj (a g) = 1) :
    ∑ ψ : AddChar H ℂ, fiberTransform a ψ 0 * conj (fiberTransform a ψ 0) =
      ((Fintype.card H * Fintype.card H : ℕ) : ℂ) := by
  have hterm : ∀ ψ : AddChar H ℂ, fiberTransform a ψ 0 * conj (fiberTransform a ψ 0) =
      ∑ h, ∑ h', a (0, h) * conj (a (0, h')) * ψ (h - h') := by
    intro ψ
    rw [conj_fiberTransform, fiberTransform, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  simp_rw [hterm]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun h _ => ?_).trans (?_ : ∑ _h : H, ((Fintype.card H : ℕ) : ℂ) = _)
  · rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, AddChar.sum_apply_eq_ite, sub_eq_zero, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    simp [hnorm]
  · simp

omit hp in
lemma norm_mul_conj_eq_one {z : ℂ} {h : ℕ} (hh : h ≠ 0) (hz : z ^ h = 1) : z * conj z = 1 := by
  have h1 : ‖z‖ = 1 := by
    have := congrArg norm hz
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hh).mp this
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
  simp

/-- **Theorem S for `C_p × H`.** -/
theorem no_perfect_prod (H : Type*) [AddCommGroup H] [Fintype H] (hpH : ¬ p ∣ Fintype.card H)
    (h : ℕ) (hph : ¬ p ∣ h) (a : ZMod p × H → ℂ) (ha : ∀ g, a g ^ h = 1)
    (hperf : ∀ s ≠ 0, ∑ g, a (g + s) * conj (a g) = 0) : False := by
  classical
  have hh0 : h ≠ 0 := by rintro rfl; exact hph (dvd_zero p)
  set M := Fintype.card H with hMdef
  have hM0 : M ≠ 0 := Fintype.card_ne_zero
  set L := h * M with hLdef
  have : NeZero L := ⟨mul_ne_zero hh0 hM0⟩
  have hpL : ¬ p ∣ L := fun hd => (hp.out.dvd_mul.mp hd).elim hph hpH
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
  have hnorm : ∀ g, a g * conj (a g) = 1 := fun g => norm_mul_conj_eq_one hh0 (ha g)
  have haL : ∀ g, a g ^ L = 1 := fun g => by rw [hLdef, pow_mul, ha, one_pow]
  have hcaL : ∀ g, conj (a g) ^ L = 1 := fun g => by rw [← map_pow, haL, map_one]
  have hψL : ∀ (ψ : AddChar H ℂ) (x : H), ψ x ^ L = 1 := by
    intro ψ x
    rw [hLdef, mul_comm, pow_mul, ← AddChar.map_nsmul_eq_pow, hMdef, card_nsmul_eq_zero,
      AddChar.map_zero_eq_one, one_pow]
  have hmem : ∀ ψ y, ∃ o, ι o = fiberTransform a ψ y := fun ψ y =>
    ι.range.sum_mem fun h _ => ι.range.mul_mem (hroot' _ (haL _)) (hroot' _ (hψL _ _))
  have hmem' : ∀ ψ y, ∃ o, ι o = conj (fiberTransform a ψ y) := by
    intro ψ y
    rw [conj_fiberTransform]
    exact ι.range.sum_mem fun h _ => ι.range.mul_mem (hroot' _ (hcaL _)) (hroot' _ (hψL _ _))
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

end OAI.CirculantHadamard.TheoremS
