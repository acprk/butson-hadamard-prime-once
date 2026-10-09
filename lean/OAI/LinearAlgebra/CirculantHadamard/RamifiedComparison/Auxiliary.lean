import Mathlib

/-!
# Auxiliary lemmas for Theorem C

* a root of unity congruent to `1` modulo an ideal of residue characteristic `p` and
  modulo an ideal of residue characteristic `q ≠ p` is `1`;
* the ratio of two pairs of elements with equal valuations and congruent leading
  digits at a prime `𝔓` is `a / s` with `s ∉ 𝔓` and `a ≡ s (mod 𝔓)`;
* an element of the fraction field of a domain which is `𝔓`-integral for every
  maximal ideal `𝔓` is integral.
-/

namespace OAI

namespace CirculantHadamard.RamifiedComparison

open IsLocalRing

/-- A root of unity `W` with `W ≡ 1` modulo ideals `I` and `J` whose prime characteristics
are `p ≠ q` equals `1`. -/
theorem eq_one_of_pow_eq_one_of_sub_one_mem {R : Type*} [CommRing R] [IsDomain R] {W : R}
    {n : ℕ} (hn : 0 < n) (hWn : W ^ n = 1) (I J : Ideal R) {p q : ℕ} (hpq : p ≠ q)
    (hI : W - 1 ∈ I) (hJ : W - 1 ∈ J)
    (hIp : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : R) ∈ I → ℓ = p)
    (hJq : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : R) ∈ J → ℓ = q) : W = 1 := by
  by_contra hW1
  have hfin : IsOfFinOrder W := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hWn⟩
  have hr0 : orderOf W ≠ 0 := (orderOf_pos_iff.2 hfin).ne'
  have hr1 : orderOf W ≠ 1 := fun h => hW1 (orderOf_eq_one_iff.1 h)
  obtain ⟨ℓ, hℓ, hℓr⟩ := Nat.exists_prime_and_dvd hr1
  set W' := W ^ (orderOf W / ℓ)
  have hW'ord : orderOf W' = ℓ := orderOf_pow_orderOf_div hr0 hℓr
  have hW'1 : W' ≠ 1 := fun h => hℓ.one_lt.ne' (by rw [← hW'ord, h, orderOf_one])
  have hW'ℓ : W' ^ ℓ = 1 := by rw [← hW'ord]; exact pow_orderOf_eq_one W'
  have hgeom : ∑ i ∈ Finset.range ℓ, W' ^ i = 0 := by
    have h := geom_sum_mul W' ℓ
    rw [hW'ℓ, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hW'1)
  have key : ∀ I : Ideal R, W - 1 ∈ I → (ℓ : R) ∈ I := by
    intro I hI
    have hmem : ∀ k : ℕ, W ^ k - 1 ∈ I := fun k => by
      obtain ⟨c, hc⟩ := sub_one_dvd_pow_sub_one W k
      rw [hc]
      exact I.mul_mem_right _ hI
    have hsum : ∑ i ∈ Finset.range ℓ, (W' ^ i - 1) ∈ I :=
      I.sum_mem fun i _ => by rw [← pow_mul]; exact hmem _
    rw [Finset.sum_sub_distrib, hgeom, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, zero_sub, neg_mem_iff] at hsum
    exact hsum
  exact hpq ((hIp ℓ hℓ (key I hI)).symm.trans (hJq ℓ hℓ (key J hJ)))

/-- **Ratio lemma.** If at a prime `𝔓` the elements `A₁, B₁` share the valuation `α`,
`A₂, B₂` share the valuation `β`, and the leading digits are congruent, then
`A₁ A₂ / (B₁ B₂) = a / s` with `s ∉ 𝔓` and `a ≡ s (mod 𝔓)`. -/
theorem exists_ratio_rep {R : Type*} [CommRing R] [IsDomain R] (𝔓 : Ideal R) [𝔓.IsPrime]
    (A₁ A₂ B₁ B₂ : R) (π : Localization.AtPrime 𝔓) (α β : ℕ)
    (g₁ g₁' g₂ g₂' : Localization.AtPrime 𝔓) (hg₁' : IsUnit g₁') (hg₂' : IsUnit g₂')
    (hA₁ : algebraMap R (Localization.AtPrime 𝔓) A₁ = π ^ α * g₁)
    (hB₁ : algebraMap R (Localization.AtPrime 𝔓) B₁ = π ^ α * g₁')
    (hA₂ : algebraMap R (Localization.AtPrime 𝔓) A₂ = π ^ β * g₂)
    (hB₂ : algebraMap R (Localization.AtPrime 𝔓) B₂ = π ^ β * g₂')
    (h₁ : g₁ - g₁' ∈ maximalIdeal (Localization.AtPrime 𝔓))
    (h₂ : g₂ - g₂' ∈ maximalIdeal (Localization.AtPrime 𝔓)) :
    ∃ a s : R, s ∉ 𝔓 ∧ B₁ * B₂ * a = A₁ * A₂ * s ∧ a - s ∈ 𝔓 := by
  set φ := algebraMap R (Localization.AtPrime 𝔓)
  obtain ⟨u₁, rfl⟩ := hg₁'
  obtain ⟨u₂, rfl⟩ := hg₂'
  set X : Localization.AtPrime 𝔓 := g₁ * g₂ * ↑(u₁ * u₂)⁻¹ with hXdef
  obtain ⟨⟨a, ⟨s, hs⟩⟩, hX⟩ := IsLocalization.mk'_surjective 𝔓.primeCompl X
  have hXs : X * φ s = φ a := by
    rw [← hX]; exact IsLocalization.mk'_spec (Localization.AtPrime 𝔓) a ⟨s, hs⟩
  have hinj : Function.Injective φ :=
    IsLocalization.injective (Localization.AtPrime 𝔓) 𝔓.primeCompl_le_nonZeroDivisors
  have hinv : (↑(u₁ * u₂)⁻¹ : Localization.AtPrime 𝔓) * (↑u₁ * ↑u₂) = 1 := by rw [← Units.val_mul, Units.inv_mul]
  have hBX : φ (B₁ * B₂) * X = φ (A₁ * A₂) := by
    rw [map_mul, map_mul, hA₁, hB₁, hA₂, hB₂]
    calc π ^ α * ↑u₁ * (π ^ β * ↑u₂) * X =
        π ^ α * π ^ β * g₁ * g₂ * ((↑(u₁ * u₂)⁻¹ : Localization.AtPrime 𝔓) * (↑u₁ * ↑u₂)) := by rw [hXdef]; ring
      _ = π ^ α * g₁ * (π ^ β * g₂) := by rw [hinv]; ring
  refine ⟨a, s, hs, hinj ?_, ?_⟩
  · rw [map_mul, ← hXs, ← mul_assoc, hBX]; simp only [map_mul]
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔓) 𝔓]
    have hX1 : X - 1 = (g₁ * (g₂ - ↑u₂) + ↑u₂ * (g₁ - ↑u₁)) * ↑(u₁ * u₂)⁻¹ := by
      rw [hXdef]
      calc g₁ * g₂ * ↑(u₁ * u₂)⁻¹ - 1 =
          g₁ * g₂ * ↑(u₁ * u₂)⁻¹ - (↑(u₁ * u₂)⁻¹ : Localization.AtPrime 𝔓) * (↑u₁ * ↑u₂) := by rw [hinv]
        _ = _ := by ring
    have hX1m : X - 1 ∈ maximalIdeal (Localization.AtPrime 𝔓) := by
      rw [hX1]
      refine Ideal.mul_mem_right _ _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ h₂)
        (Ideal.mul_mem_left _ _ h₁))
    have : φ (a - s) = (X - 1) * φ s := by rw [map_sub, ← hXs]; ring
    rw [this]
    exact Ideal.mul_mem_right _ _ hX1m

/-- An element of the fraction field which is `𝔓`-integral at every maximal ideal `𝔓`
lies in the ring. -/
theorem mem_range_of_forall_maximal {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] (x : K)
    (hx : ∀ 𝔓 : Ideal R, 𝔓.IsMaximal → ∃ a s : R, s ∉ 𝔓 ∧ x = algebraMap R K a / algebraMap R K s) :
    ∃ r : R, algebraMap R K r = x := by
  have hmem : x ∈ (⨅ v : MaximalSpectrum R,
      Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) := by
    rw [Algebra.mem_iInf]
    intro v
    obtain ⟨a, s, hs, rfl⟩ := hx v.asIdeal v.isMaximal
    exact ⟨a, s, hs, by rw [div_eq_mul_inv]⟩
  rw [MaximalSpectrum.iInf_localization_eq_bot, Algebra.mem_bot] at hmem
  obtain ⟨r, hr⟩ := hmem
  exact ⟨r, hr⟩

end CirculantHadamard.RamifiedComparison

end OAI
