import Mathlib

/-!
# Theorem S, arithmetic input: an unramified prime in `ℤ[ζ_L]`

For a prime `p ∤ L` we produce a maximal ideal `P` of `O = 𝓞 (CyclotomicField L ℚ)` with
`p ∈ P` and `p ∉ P ^ 2`.  This uses Mathlib's
`IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd` (Dedekind–Kummer for cyclotomic
fields).  We also record the elementary consequences used by the core argument, and an
injective ring map `O →+* ℂ`.
-/

namespace OAI.CirculantHadamard.TheoremS

open NumberField

/-- **Unramified prime.**  If `p ∤ L`, some maximal ideal `P` of `ℤ[ζ_L]` contains `p` but not
`p ^ 2`-adically: `p ∉ P ^ 2`. -/
theorem exists_unramified_prime (L p : ℕ) [NeZero L] [hp : Fact p.Prime] (hpL : ¬ p ∣ L) :
    ∃ P : Ideal (𝓞 (CyclotomicField L ℚ)), P.IsMaximal ∧
      ((p : 𝓞 (CyclotomicField L ℚ)) ∈ P) ∧ ((p : 𝓞 (CyclotomicField L ℚ)) ∉ P ^ 2) := by
  have : IsCyclotomicExtension {L} ℚ (CyclotomicField L ℚ) :=
    CyclotomicField.isCyclotomicExtension L ℚ
  obtain ⟨⟨P, hPprime, hPover⟩⟩ :=
    (Ideal.span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 (CyclotomicField L ℚ))
  have hram : P.ramificationIdx ℤ = 1 :=
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p (CyclotomicField L ℚ) P hpL
  have hspan : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  have hram' : (Ideal.span {(p : ℤ)}).ramificationIdx' P = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ P hspan, hram]
  have hmapP : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 (CyclotomicField L ℚ))) ≤ P := by
    rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def, ← Ideal.over_def P (Ideal.span {(p : ℤ)})]
  have hpP : (p : 𝓞 (CyclotomicField L ℚ)) ∈ P := by
    apply hmapP
    have : (p : 𝓞 (CyclotomicField L ℚ)) =
        algebraMap ℤ (𝓞 (CyclotomicField L ℚ)) (p : ℤ) := by simp
    rw [this]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
  have hPmax : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(p : ℤ)})
  refine ⟨P, hPmax, hpP, fun hp2 => ?_⟩
  have hle : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 (CyclotomicField L ℚ))) ≤ P ^ 2 := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    simpa using hp2
  exact (Ideal.ramificationIdx'_ne_one_iff hmapP).mpr hle hram'

/-- A natural number prime to `p` is not in an ideal `P ≠ ⊤` containing `p`. -/
theorem natCast_notMem {O : Type*} [CommRing O] (P : Ideal O) (hP : P ≠ ⊤) {p M : ℕ}
    (hpP : (p : O) ∈ P) (hcop : Nat.Coprime p M) : (M : O) ∉ P := by
  intro hM
  apply hP
  rw [Ideal.eq_top_iff_one]
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr hcop)
  have : (1 : O) = (u : O) * p + (v : O) * M := by
    have := congrArg (Int.cast : ℤ → O) huv
    push_cast at this
    exact this.symm
  rw [this]
  exact P.add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hM)

/-- In a Dedekind domain, if `p ∉ P ^ 2` and `M ∉ P` then `p * M ∉ P ^ 2`. -/
theorem mul_notMem_sq {O : Type*} [CommRing O] [IsDedekindDomain O] (P : Ideal O) [P.IsPrime]
    {a b : O} (ha : a ∉ P ^ 2) (hb : b ∉ P) : a * b ∉ P ^ 2 := by
  intro h
  rcases Ideal.IsPrime.mem_pow_mul P h with h | h
  · exact ha h
  · exact hb h

/-- The ring of integers of a number field embeds into `ℂ`. -/
theorem exists_injective_toComplex (K : Type*) [Field K] [NumberField K] :
    ∃ ι : 𝓞 K →+* ℂ, Function.Injective ι := by
  let φ : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
  refine ⟨(φ : K →+* ℂ).comp (algebraMap (𝓞 K) K), ?_⟩
  exact (φ : K →+* ℂ).injective.comp (RingOfIntegers.coe_injective)

end OAI.CirculantHadamard.TheoremS
