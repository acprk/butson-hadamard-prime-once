import OAI.LinearAlgebra.CirculantHadamard.RamifiedComparison.Core

/-!
# Lemma A at an arbitrary prime above `p`

Let `K` be a number field and `P` a prime of `𝓞 K` above the rational prime `p` with
ramification index `p - 1`, and let `y ∈ 𝓞 K` with `y ^ (p - 1)` associated to `p`
(e.g. `y = ζ_p - 1`). Then `y` is a uniformizer of the discrete valuation ring
`(𝓞 K)_P`, and the abstract core of Lemma A applies in `(𝓞 K)_P`.

This covers `𝓞 K = ℤ[ζ_p, ζ_d]` with `p ∤ d` (whose primes above `p` have ramification
index `p - 1`), i.e. Lemma A for general `d`.
-/

namespace OAI

namespace CirculantHadamard.RamifiedComparison

open NumberField IsLocalRing

variable {K : Type*} [Field K] [NumberField K]

/-- `y` is a uniformizer at `P` when `y ^ (p - 1) ∼ p` and `e(P | p) = p - 1`. -/
theorem maximalIdeal_eq_span_of_ramificationIdx (p : ℕ) [hp : Fact p.Prime]
    (P : Ideal (𝓞 K)) [hP : P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (he : P.ramificationIdx ℤ = p - 1) (y : 𝓞 K) (hy : Associated (y ^ (p - 1)) (p : 𝓞 K)) :
    maximalIdeal (Localization.AtPrime P) =
      Ideal.span {algebraMap (𝓞 K) (Localization.AtPrime P) y} := by
  set S := Localization.AtPrime P
  have hp1 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
  have hpP : ((p : ℤ) : 𝓞 K) ∈ P := by
    have : (p : ℤ) ∈ P.under ℤ := by
      rw [← Ideal.over_def P (Ideal.span {(p : ℤ)})]
      exact Ideal.subset_span rfl
    simpa using this
  have hp0 : (p : 𝓞 K) ≠ 0 := NeZero.natCast_ne p (𝓞 K)
  have hP0 : P ≠ ⊥ := fun h => hp0 (by rw [h] at hpP; simpa using hpP)
  have hDVR : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) hP0 S
  have hinj : Function.Injective (algebraMap (𝓞 K) S) :=
    IsLocalization.injective S P.primeCompl_le_nonZeroDivisors
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hy
    exact hp0 (hy.eq_zero_iff.1 rfl)
  have hy0' : algebraMap (𝓞 K) S y ≠ 0 := (map_ne_zero_iff _ hinj).2 hy0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {algebraMap (𝓞 K) S y}) (by rwa [Ne, Ideal.span_singleton_eq_bot]) hϖ
  have hmax : maximalIdeal S = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  -- the image of `(p)` in `S` is `𝔪 ^ (k (p - 1))`
  have hmap : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ S) = maximalIdeal S ^ (k * (p - 1)) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast, hmax, Ideal.span_singleton_pow,
      pow_mul, ← Ideal.span_singleton_pow, ← hk, Ideal.span_singleton_pow]
    refine Ideal.span_singleton_eq_span_singleton.2 ?_
    have := hy.map (algebraMap (𝓞 K) S)
    rw [map_pow, map_natCast] at this
    exact this.symm
  have hlen := Ideal.ramificationIdx_eq (Ideal.span {(p : ℤ)}) P
  rw [hmap, hDVR.length_quotient_pow_maximalIdeal, ENat.toNat_natCast, he] at hlen
  have hk1 : k = 1 := by
    have : (k - 1) * (p - 1) = 0 := by rw [Nat.sub_mul, ← hlen]; simp
    rcases Nat.mul_eq_zero.1 this with h | h
    · rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0
        rw [zero_mul] at hlen
        omega
      · omega
    · omega
  rw [hmax, ← pow_one ϖ, ← hk1, ← hk]

/-- **Lemma A, localized form.** Exponential sums `f, f'` over `𝓞 K` with ratios
`≡ 1 (mod y)` and `f j * f' j = p * m` (`m ∉ P`) for all `j < p`. Then in `(𝓞 K)_P`
there is `α` with `f j = y ^ α * g j`, every `g j` a unit, and `g j ≡ g 0`. -/
theorem lemmaA_localized (p : ℕ) [hp : Fact p.Prime]
    (P : Ideal (𝓞 K)) [hP : P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (he : P.ramificationIdx ℤ = p - 1) (y : 𝓞 K) (hy : Associated (y ^ (p - 1)) (p : 𝓞 K))
    {ι κ : Type*} (s : Finset ι) (t : Finset κ) (c r : ι → 𝓞 K) (c' r' : κ → 𝓞 K)
    (hr : ∀ i ∈ s, y ∣ r i - 1) (hr' : ∀ i ∈ t, y ∣ r' i - 1) (m : 𝓞 K) (hm : m ∉ P)
    (hprod : ∀ j < p, (∑ i ∈ s, c i * r i ^ j) * (∑ i ∈ t, c' i * r' i ^ j) = (p : 𝓞 K) * m) :
    ∃ (α : ℕ) (g : ℕ → Localization.AtPrime P), ∀ j < p,
      IsUnit (g j) ∧
      algebraMap (𝓞 K) (Localization.AtPrime P) (∑ i ∈ s, c i * r i ^ j) =
        algebraMap (𝓞 K) (Localization.AtPrime P) y ^ α * g j ∧
      g j - g 0 ∈ maximalIdeal (Localization.AtPrime P) := by
  classical
  set S := Localization.AtPrime P
  set φ := algebraMap (𝓞 K) S
  have hmaxeq := maximalIdeal_eq_span_of_ramificationIdx p P he y hy
  have hp0 : (p : 𝓞 K) ≠ 0 := NeZero.natCast_ne p (𝓞 K)
  have hinj : Function.Injective φ := IsLocalization.injective S P.primeCompl_le_nonZeroDivisors
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow (by have := hp.out.two_le; omega)] at hy
    exact hp0 (hy.eq_zero_iff.1 rfl)
  have hy0' : φ y ≠ 0 := (map_ne_zero_iff _ hinj).2 hy0
  have hmax : (Ideal.span {φ y}).IsMaximal := hmaxeq ▸ maximalIdeal.isMaximal S
  have hmemmax : ∀ x : S, φ y ∣ x ↔ x ∈ maximalIdeal S := fun x => by
    rw [hmaxeq, Ideal.mem_span_singleton]
  obtain ⟨w, hw⟩ := hy
  have hpy : φ y ∣ (p : S) := by
    rw [← map_natCast φ, ← hw, map_mul, map_pow]
    exact (dvd_pow_self _ (by have := hp.out.two_le; omega)).mul_right _
  have hν : ¬ φ y ∣ φ ((w : 𝓞 K) * m) := by
    rw [hmemmax, IsLocalization.AtPrime.to_map_mem_maximal_iff S P]
    intro h
    rcases hP.mem_or_mem h with h | h
    · exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h w.isUnit)
    · exact hm h
  obtain ⟨α, hα⟩ := ramified_comparison_core p hp.out (φ y) hy0' hmax hpy s t
    (fun i => φ (c i)) (fun i => φ (r i)) (fun i => φ (c' i)) (fun i => φ (r' i))
    (fun i hi => by rw [← map_one φ, ← map_sub]; exact map_dvd φ (hr i hi))
    (fun i hi => by rw [← map_one φ, ← map_sub]; exact map_dvd φ (hr' i hi))
    (φ ((w : 𝓞 K) * m)) hν
    (fun j hj => by
      have := congrArg φ (hprod j hj)
      simp only [map_mul, map_sum, map_pow, map_natCast] at this
      rw [this, ← map_natCast φ, ← hw]
      simp only [map_mul, map_pow]
      ring)
  have hφsum : ∀ j, φ (∑ i ∈ s, c i * r i ^ j) = ∑ i ∈ s, φ (c i) * φ (r i) ^ j := fun j => by
    simp [map_sum, map_mul, map_pow]
  have hdiv : ∀ j < p, ∃ g : S, φ (∑ i ∈ s, c i * r i ^ j) = φ y ^ α * g := fun j hj => by
    rw [hφsum]; exact (hα j hj).1
  choose! g hg using hdiv
  refine ⟨α, g, fun j hj => ⟨?_, hg j hj, ?_⟩⟩
  · by_contra hu
    have hmem : g j ∈ maximalIdeal S := (IsLocalRing.mem_maximalIdeal _).2 hu
    rw [← hmemmax] at hmem
    apply (hα j hj).2.1
    rw [← hφsum, hg j hj, pow_succ]
    exact mul_dvd_mul_left _ hmem
  · rw [← hmemmax]
    have h2 := (hα j hj).2.2
    rw [← hφsum, ← hφsum, hg j hj, hg 0 hp.out.pos, ← mul_sub, pow_succ] at h2
    exact (mul_dvd_mul_iff_left (pow_ne_zero α hy0')).1 h2

end CirculantHadamard.RamifiedComparison

end OAI
