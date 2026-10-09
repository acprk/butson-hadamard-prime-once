import OAI.LinearAlgebra.CirculantHadamard.RamifiedComparison.Localized
import OAI.LinearAlgebra.CirculantHadamard.RamifiedComparison.PrimeCyclotomic

/-!
# Lemma A (ramified comparison) over `ℤ[ζ_p, ζ_d]`

Let `p` be a prime, `p ∤ d`, `K = ℚ(ζ_{pd})` and `O = 𝓞 K = ℤ[ζ_p, ζ_d]`. Let
`F, V ∈ O[C_p]` with `F * V = n` (convolution), where `n ∈ ℤ` and `v_p(n) = 1`.
Then for every prime `P` of `O` above `p` there is `α` such that for all `j`:

* `F(ζ_p^j) ∈ P ^ α` and `F(ζ_p^j) ∉ P ^ (α + 1)`, i.e. `v_P(F(ζ_p^j)) = α` does not
  depend on `j`;
* `F(ζ_p^j) - F(1) ∈ P ^ (α + 1)`, i.e. `F(ζ_p^j) / F(1) ≡ 1 (mod P)`.

With `V = F^*` this is exactly Lemma A of the ramified comparison (no conjugation, and
no hypothesis `P = P̄`, is needed).
-/

namespace OAI

namespace CirculantHadamard.RamifiedComparison

open NumberField IsLocalRing

variable {K : Type*} [Field K] [NumberField K]

/-- Membership in powers of `P` is divisibility by powers of a uniformizer of `(𝓞 K)_P`. -/
theorem mem_pow_iff_dvd (P : Ideal (𝓞 K)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) (y : 𝓞 K)
    (hmax : maximalIdeal (Localization.AtPrime P) =
      Ideal.span {algebraMap (𝓞 K) (Localization.AtPrime P) y})
    (k : ℕ) (x : 𝓞 K) :
    x ∈ P ^ k ↔
      algebraMap (𝓞 K) (Localization.AtPrime P) y ^ k ∣
        algebraMap (𝓞 K) (Localization.AtPrime P) x := by
  set S := Localization.AtPrime P
  have hmapk : (P ^ k).map (algebraMap (𝓞 K) S) =
      Ideal.span {algebraMap (𝓞 K) S y ^ k} := by
    rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal, hmax, Ideal.span_singleton_pow]
  have hPmax : P.IsMaximal := hP.isMaximal hP0
  rw [← Ideal.mem_span_singleton, ← hmapk]
  constructor
  · exact Ideal.mem_map_of_mem _
  · intro hx
    by_cases hk : k = 0
    · subst hk; simp
    have hprim : (P ^ k).IsPrimary := by
      apply Ideal.isPrimary_of_isMaximal_radical
      rw [Ideal.radical_pow P hk, hP.radical]
      exact hPmax
    have hdisj : Disjoint (P.primeCompl : Set (𝓞 K)) (P ^ k : Ideal (𝓞 K)) := by
      rw [Set.disjoint_left]
      intro a ha ha'
      exact ha (Ideal.pow_le_self hk ha')
    have := IsLocalization.under_map_of_isPrimary_disjoint P.primeCompl S hprim hdisj
    rw [← this]
    exact hx

/-- **Lemma A.** -/
theorem lemmaA (p d : ℕ) [hp : Fact p.Prime] (hd : ¬ p ∣ d)
    [IsCyclotomicExtension {p * d} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (P : Ideal (𝓞 K)) [hP : P.IsPrime] [hPo : P.LiesOver (Ideal.span {(p : ℤ)})]
    (u v : ZMod p → 𝓞 K) (n : ℤ) (hn₁ : (p : ℤ) ∣ n) (hn₂ : ¬ (p : ℤ) ^ 2 ∣ n)
    (huv : ∀ τ : ZMod p, ∑ a, u a * v (τ - a) = if τ = 0 then (n : 𝓞 K) else 0) :
    ∃ α : ℕ, ∀ j : ℕ,
      ∑ a, u a * hζ.toInteger ^ (j * a.val) ∈ P ^ α ∧
      ∑ a, u a * hζ.toInteger ^ (j * a.val) ∉ P ^ (α + 1) ∧
      (∑ a, u a * hζ.toInteger ^ (j * a.val)) - ∑ a, u a ∈ P ^ (α + 1) := by
  set S := Localization.AtPrime P
  set φ := algebraMap (𝓞 K) S
  set y : 𝓞 K := hζ.toInteger - 1 with hy_def
  have hy := IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hζ
  have he : P.ramificationIdx ℤ = p - 1 := by
    have := IsCyclotomicExtension.Rat.ramificationIdx_eq (p * d) K P
      (show p * d = p ^ (0 + 1) * d by ring) hd
    rwa [pow_zero, one_mul] at this
  have hmax := maximalIdeal_eq_span_of_ramificationIdx p P he y hy
  have hpP : ((p : ℤ) : 𝓞 K) ∈ P := by
    have : (p : ℤ) ∈ P.under ℤ := by
      rw [← Ideal.over_def P (Ideal.span {(p : ℤ)})]
      exact Ideal.subset_span rfl
    simpa using this
  have hp0 : (p : 𝓞 K) ≠ 0 := NeZero.natCast_ne p (𝓞 K)
  have hP0 : P ≠ ⊥ := fun h => hp0 (by rw [h] at hpP; simpa using hpP)
  -- `n = p * m` with `m ∉ P`
  obtain ⟨m, rfl⟩ := hn₁
  have hm : ¬ (p : ℤ) ∣ m := fun h => hn₂ (by rw [pow_two]; exact mul_dvd_mul_left _ h)
  have hmP : ((m : ℤ) : 𝓞 K) ∉ P := by
    intro h
    apply hm
    have : m ∈ P.under ℤ := by simpa using h
    rw [← Ideal.over_def P (Ideal.span {(p : ℤ)}), Ideal.mem_span_singleton] at this
    exact this
  have hprod : ∀ j < p,
      (∑ a, u a * (hζ.toInteger ^ a.val) ^ j) * (∑ b, v b * (hζ.toInteger ^ b.val) ^ j) =
        (p : 𝓞 K) * ((m : ℤ) : 𝓞 K) := by
    intro j _
    rw [eval_mul_eval hζ, Fintype.sum_eq_single 0 (fun τ hτ => by simp [huv τ, hτ])]
    simp only [huv 0, ↓reduceIte]
    rw [ZMod.val_zero, pow_zero, one_pow, mul_one]
    push_cast; ring
  obtain ⟨α, g, hg⟩ := lemmaA_localized p P he y hy Finset.univ Finset.univ
    u (fun a => hζ.toInteger ^ a.val) v (fun b => hζ.toInteger ^ b.val)
    (fun a _ => by simpa [one_pow] using sub_dvd_pow_sub_pow hζ.toInteger 1 a.val)
    (fun b _ => by simpa [one_pow] using sub_dvd_pow_sub_pow hζ.toInteger 1 b.val)
    _ hmP hprod
  have hiff := mem_pow_iff_dvd P hP0 y hmax
  have hinj : Function.Injective φ := IsLocalization.injective S P.primeCompl_le_nonZeroDivisors
  have hy0 : y ≠ 0 := by
    intro h0
    have hy2 := hy
    rw [← hy_def, h0, zero_pow (by have := hp.out.two_le; omega)] at hy2
    exact hp0 (hy2.eq_zero_iff.1 rfl)
  have hy0' : φ y ≠ 0 := (map_ne_zero_iff _ hinj).2 hy0
  have hy' : ¬ IsUnit (φ y) := by
    have : φ y ∈ maximalIdeal S := by rw [hmax]; exact Ideal.mem_span_singleton_self _
    exact (IsLocalRing.mem_maximalIdeal _).1 this
  refine ⟨α, fun j => ?_⟩
  have hred : ∀ a : ZMod p, hζ.toInteger ^ (j * a.val) = (hζ.toInteger ^ a.val) ^ (j % p) := by
    intro a
    rw [← pow_mul, toInteger_pow_mod hζ (j * a.val), toInteger_pow_mod hζ (a.val * (j % p))]
    congr 1
    conv_rhs => rw [mul_comm, Nat.mod_mul_mod]
  simp_rw [hred]
  have h0 : ∑ a, u a = ∑ a, u a * (hζ.toInteger ^ a.val) ^ 0 := by simp
  rw [h0]
  have hjp : j % p < p := Nat.mod_lt _ hp.out.pos
  obtain ⟨hu, heq, hres⟩ := hg (j % p) hjp
  obtain ⟨-, heq0, -⟩ := hg 0 hp.out.pos
  refine ⟨(hiff α _).2 ⟨g (j % p), heq⟩, fun hmem => ?_, ?_⟩
  · rw [hiff, heq, pow_succ] at hmem
    have := (mul_dvd_mul_iff_left (pow_ne_zero α hy0')).1 hmem
    exact hy' (isUnit_of_dvd_unit this hu)
  · rw [hiff, show φ ((∑ x, u x * (hζ.toInteger ^ x.val) ^ (j % p)) -
        ∑ a, u a * (hζ.toInteger ^ a.val) ^ 0) = φ (∑ x, u x * (hζ.toInteger ^ x.val) ^ (j % p)) -
        φ (∑ a, u a * (hζ.toInteger ^ a.val) ^ 0) from map_sub _ _ _, heq, heq0, ← mul_sub,
      pow_succ]
    refine mul_dvd_mul_left _ ?_
    rw [← Ideal.mem_span_singleton, ← hmax]
    exact hres

end CirculantHadamard.RamifiedComparison

end OAI
