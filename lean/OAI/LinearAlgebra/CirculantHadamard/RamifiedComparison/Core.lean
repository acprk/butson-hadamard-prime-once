import Mathlib

/-!
# Ramified comparison: the abstract core of Lemma A

Let `A` be a domain and `y ∈ A` an element generating a maximal ideal whose residue
field has characteristic `p`. Consider two "exponential sums"
`f j = ∑ᵢ cᵢ rᵢ ^ j` and `f' j = ∑ᵢ c'ᵢ r'ᵢ ^ j` with all `rᵢ, r'ᵢ ≡ 1 (mod y)`,
and suppose `f j * f' j = y ^ (p - 1) * ν` for every `j < p`, where `y ∤ ν`.

Then the `y`-adic valuation `α` of `f j` does not depend on `j < p`, and moreover
`f j ≡ f 0 (mod y ^ (α + 1))`.

The proof: by the binomial theorem `f j = ∑ₖ (j choose k) Dₖ` with `y ^ k ∣ Dₖ`,
so the leading `y`-adic digit of `f j` is the value at `j` of a polynomial of degree
`≤ α` over the residue field. Comparing the two digit polynomials (their degrees add
up to at most `p - 1` while they are evaluated at the `p` distinct points
`0, …, p - 1`) forces the valuations to be constant and the digit polynomial to be
constant.

Applied with `A` the localization of `ℤ[ζ_p, ζ_d]` at a prime above `p`, `y = ζ_p - 1`,
`rᵢ = ζ_p ^ i` and `f' = f^*`, this is Lemma A of the ramified comparison.
-/

namespace OAI

namespace CirculantHadamard.RamifiedComparison

open Polynomial Finset

section Valuation

variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in
/-- If `y ^ N ∤ x`, then `x` has an exact `y`-adic valuation `< N`. -/
theorem exists_exact_pow_dvd (y x : A) (N : ℕ) (hN : ¬ y ^ N ∣ x) :
    ∃ a < N, y ^ a ∣ x ∧ ¬ y ^ (a + 1) ∣ x := by
  induction N with
  | zero => exact absurd (by simp) hN
  | succ N ih =>
    by_cases h : y ^ N ∣ x
    · exact ⟨N, Nat.lt_succ_self N, h, hN⟩
    · obtain ⟨a, ha, h1, h2⟩ := ih h
      exact ⟨a, Nat.lt_succ_of_lt ha, h1, h2⟩

omit [IsDomain A] in
/-- Exact valuations are unique. -/
theorem exact_pow_dvd_unique {y x : A} {a b : ℕ} (ha : y ^ a ∣ x) (ha' : ¬ y ^ (a + 1) ∣ x)
    (hb : y ^ b ∣ x) (hb' : ¬ y ^ (b + 1) ∣ x) : a = b := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact ha' ((pow_dvd_pow y h).trans hb)
  · exact hb' ((pow_dvd_pow y h).trans ha)

/-- Cancellation of powers of a nonzero `y` against non-multiples of `y`. -/
theorem pow_eq_of_mul_eq {y u v : A} (hy : y ≠ 0) {m n : ℕ} (hu : ¬ y ∣ u) (hv : ¬ y ∣ v)
    (h : y ^ m * u = y ^ n * v) : m = n := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hmn | hmn
  · apply hu
    have : y ^ m * u = y ^ m * (y ^ (n - m) * v) := by
      rw [h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hmn.le]
    rw [mul_left_cancel₀ (pow_ne_zero m hy) this]
    exact (dvd_pow_self y (Nat.sub_ne_zero_of_lt hmn)).mul_right v
  · apply hv
    have : y ^ n * v = y ^ n * (y ^ (m - n) * u) := by
      rw [← h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hmn.le]
    rw [mul_left_cancel₀ (pow_ne_zero n hy) this]
    exact (dvd_pow_self y (Nat.sub_ne_zero_of_lt hmn)).mul_right u

end Valuation

section Newton

variable {A : Type*} [CommRing A]

/-- Newton expansion of an exponential sum. -/
theorem expSum_eq_sum_choose {ι : Type*} (s : Finset ι) (c r : ι → A) (j : ℕ) :
    ∑ i ∈ s, c i * r i ^ j =
      ∑ k ∈ range (j + 1), (j.choose k : A) * ∑ i ∈ s, c i * (r i - 1) ^ k := by
  have hr : ∀ i, r i ^ j = ∑ k ∈ range (j + 1), (j.choose k : A) * (r i - 1) ^ k := by
    intro i
    have := add_pow (r i - 1) 1 j
    rw [sub_add_cancel] at this
    rw [this]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_comm]
  simp_rw [hr, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The Newton expansion with the range extended to any bound `N > j`. -/
theorem expSum_eq_sum_choose' {ι : Type*} (s : Finset ι) (c r : ι → A) {j N : ℕ} (hj : j < N) :
    ∑ i ∈ s, c i * r i ^ j =
      ∑ k ∈ range N, (j.choose k : A) * ∑ i ∈ s, c i * (r i - 1) ^ k := by
  rw [expSum_eq_sum_choose]
  refine Finset.sum_subset (Finset.range_subset_range.2 hj) fun k _ hk => ?_
  rw [Finset.mem_range, not_lt] at hk
  rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

end Newton

section Core

variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in
/-- The `k`-th Newton coefficient of an exponential sum is divisible by `y ^ k`. -/
theorem pow_dvd_newton {ι : Type*} (s : Finset ι) (c r : ι → A) (y : A)
    (hr : ∀ i ∈ s, y ∣ r i - 1) (k : ℕ) :
    y ^ k ∣ ∑ i ∈ s, c i * (r i - 1) ^ k :=
  Finset.dvd_sum fun i hi => (pow_dvd_pow_of_dvd (hr i hi) k).mul_left _

omit [IsDomain A] in
/-- If every value `f j`, `j < p`, is divisible by `z`, then so is every Newton
coefficient of index `< p`. -/
theorem dvd_newton_of_dvd_values {ι : Type*} (s : Finset ι) (c r : ι → A) (z : A) (p : ℕ)
    (hf : ∀ j < p, z ∣ ∑ i ∈ s, c i * r i ^ j) :
    ∀ k < p, z ∣ ∑ i ∈ s, c i * (r i - 1) ^ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have h := expSum_eq_sum_choose s c r k
    rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul] at h
    have : ∑ i ∈ s, c i * (r i - 1) ^ k =
        ∑ i ∈ s, c i * r i ^ k -
          ∑ x ∈ range k, (k.choose x : A) * ∑ i ∈ s, c i * (r i - 1) ^ x := by
      rw [h]; ring
    rw [this]
    refine dvd_sub (hf k hk) (Finset.dvd_sum fun x hx => ?_)
    exact (ih x (Finset.mem_range.1 hx) (by have := Finset.mem_range.1 hx; omega)).mul_left _

/-- The residue-field polynomial whose values are the leading digits. -/
noncomputable def digitPoly {K : Type*} [Field K] (α : ℕ) (e : ℕ → K) : K[X] :=
  ∑ k ∈ range (α + 1), C (e k * ((k.factorial : K))⁻¹) * descPochhammer K k

theorem digitPoly_natDegree_le {K : Type*} [Field K] (α : ℕ) (e : ℕ → K) :
    (digitPoly α e).natDegree ≤ α := by
  unfold digitPoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [descPochhammer_natDegree]
  exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)

theorem digitPoly_eval {K : Type*} [Field K] (p : ℕ) [CharP K p] (hp : p.Prime) (α : ℕ)
    (hα : α < p) (e : ℕ → K) (j : ℕ) :
    (digitPoly α e).eval (j : K) = ∑ k ∈ range (α + 1), (j.choose k : K) * e k := by
  unfold digitPoly
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < p := lt_of_le_of_lt (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hα
  have hfac : ((k.factorial : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K p]
    intro h
    exact absurd ((Nat.Prime.dvd_factorial hp).1 h) (by omega)
  rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  field_simp

/-- The leading `y`-adic digit of an exponential sum is the value of the digit polynomial. -/
theorem digit_eq_eval {K : Type*} [Field K] (p : ℕ) [CharP K p] (hp : p.Prime) (π : A →+* K)
    (y : A) (hy : y ≠ 0) (hπy : π y = 0) {ι' : Type*} (s' : Finset ι') (c₀ r₀ : ι' → A)
    (hr₀ : ∀ i ∈ s', y ∣ r₀ i - 1) (γ : ℕ) (hγ : γ < p) (E₀ : ℕ → A)
    (hE₀ : ∀ k < p, ∑ i ∈ s', c₀ i * (r₀ i - 1) ^ k = y ^ γ * E₀ k)
    (j : ℕ) (hj : j < p) (g₀ : A) (hg₀ : ∑ i ∈ s', c₀ i * r₀ i ^ j = y ^ γ * g₀) :
    π g₀ = (digitPoly γ (fun k => π (E₀ k))).eval (j : K) := by
  rw [digitPoly_eval p hp γ hγ]
  have hsplit := expSum_eq_sum_choose' s' c₀ r₀ hj
  rw [← Finset.sum_range_add_sum_Ico _ (show γ + 1 ≤ p by omega)] at hsplit
  have htail : y ^ (γ + 1) ∣ ∑ k ∈ Finset.Ico (γ + 1) p,
      (j.choose k : A) * ∑ i ∈ s', c₀ i * (r₀ i - 1) ^ k := by
    refine Finset.dvd_sum fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    exact ((pow_dvd_pow y hk.1).trans (pow_dvd_newton s' c₀ r₀ y hr₀ k)).mul_left _
  obtain ⟨w, hw⟩ := htail
  have hhead : ∑ k ∈ range (γ + 1), (j.choose k : A) * ∑ i ∈ s', c₀ i * (r₀ i - 1) ^ k =
      y ^ γ * ∑ k ∈ range (γ + 1), (j.choose k : A) * E₀ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hE₀ k (by have := Finset.mem_range.1 hk; omega)]; ring
  rw [hhead, hw, hg₀, pow_succ] at hsplit
  have : g₀ = ∑ k ∈ range (γ + 1), (j.choose k : A) * E₀ k + y * w := by
    apply mul_left_cancel₀ (pow_ne_zero γ hy)
    rw [hsplit]; ring
  rw [this, map_add, map_mul, hπy, zero_mul, add_zero, map_sum]
  simp [map_mul, map_natCast]

/-- **Core of Lemma A.** -/
theorem ramified_comparison_core (p : ℕ) (hp : p.Prime) (y : A) (hy : y ≠ 0)
    (hmax : (Ideal.span {y}).IsMaximal) (hpy : y ∣ (p : A))
    {ι κ : Type*} (s : Finset ι) (t : Finset κ) (c r : ι → A) (c' r' : κ → A)
    (hr : ∀ i ∈ s, y ∣ r i - 1) (hr' : ∀ i ∈ t, y ∣ r' i - 1)
    (ν : A) (hν : ¬ y ∣ ν)
    (hprod : ∀ j < p, (∑ i ∈ s, c i * r i ^ j) * (∑ i ∈ t, c' i * r' i ^ j) = y ^ (p - 1) * ν) :
    ∃ α : ℕ, ∀ j < p,
      y ^ α ∣ ∑ i ∈ s, c i * r i ^ j ∧ ¬ y ^ (α + 1) ∣ ∑ i ∈ s, c i * r i ^ j ∧
        y ^ (α + 1) ∣ (∑ i ∈ s, c i * r i ^ j) - ∑ i ∈ s, c i * r i ^ 0 := by
  classical
  set f : ℕ → A := fun j => ∑ i ∈ s, c i * r i ^ j with hf_def
  set f' : ℕ → A := fun j => ∑ i ∈ t, c' i * r' i ^ j with hf'_def
  have hprime : Prime y := (Ideal.span_singleton_prime hy).1 hmax.isPrime
  -- the residue field
  let _ : Field (A ⧸ Ideal.span {y}) := Ideal.Quotient.field _
  set π : A →+* A ⧸ Ideal.span {y} := Ideal.Quotient.mk _ with hπ
  have hπ0 : ∀ x, π x = 0 ↔ y ∣ x := fun x => by
    rw [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have : CharP (A ⧸ Ideal.span {y}) p := by
    rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast π, hπ0]
    exact hpy
  have hp0 : 0 < p := hp.pos
  have hinj : Function.Injective fun i : Fin p => ((i : ℕ) : A ⧸ Ideal.span {y}) := by
    intro i i' h
    have := (CharP.natCast_eq_natCast (A ⧸ Ideal.span {y}) p).1 h
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt this i.2 i'.2)
  -- each value has an exact valuation, and the valuations are complementary
  have hne : ∀ j < p, ¬ y ^ p ∣ f j := by
    intro j hj hdvd
    apply hν
    have h1 : y ^ p ∣ y ^ (p - 1) * ν := by rw [← hprod j hj]; exact hdvd.mul_right _
    rw [show p = (p - 1) + 1 by omega, pow_succ] at h1
    exact (mul_dvd_mul_iff_left (pow_ne_zero _ hy)).1 h1
  have hne' : ∀ j < p, ¬ y ^ p ∣ f' j := by
    intro j hj hdvd
    apply hν
    have h1 : y ^ p ∣ y ^ (p - 1) * ν := by rw [← hprod j hj]; exact hdvd.mul_left _
    rw [show p = (p - 1) + 1 by omega, pow_succ] at h1
    exact (mul_dvd_mul_iff_left (pow_ne_zero _ hy)).1 h1
  choose! a ha using fun j (hj : j < p) => exists_exact_pow_dvd y (f j) p (hne j hj)
  choose! b hb using fun j (hj : j < p) => exists_exact_pow_dvd y (f' j) p (hne' j hj)
  have hprod' : ∀ j < p, f j * f' j = y ^ (p - 1) * ν := hprod
  have hab : ∀ j < p, a j + b j = p - 1 := by
    intro j hj
    obtain ⟨-, ⟨u, hu⟩, hu'⟩ := ha j hj
    obtain ⟨-, ⟨u', hu''⟩, hu'''⟩ := hb j hj
    have hyu : ¬ y ∣ u := fun h => hu' (by rw [hu, pow_succ]; exact mul_dvd_mul_left _ h)
    have hyu' : ¬ y ∣ u' := fun h => hu''' (by rw [hu'', pow_succ]; exact mul_dvd_mul_left _ h)
    have hyuu : ¬ y ∣ u * u' := fun h => (hprime.dvd_or_dvd h).elim hyu hyu'
    apply pow_eq_of_mul_eq hy hyuu hν
    rw [← hprod' j hj, hu, hu'', pow_add]; ring
  -- minimal valuations
  obtain ⟨j₁, hj₁, hmin₁⟩ := Finset.exists_min_image (range p) a ⟨0, Finset.mem_range.2 hp0⟩
  obtain ⟨j₂, hj₂, hmin₂⟩ := Finset.exists_min_image (range p) b ⟨0, Finset.mem_range.2 hp0⟩
  rw [Finset.mem_range] at hj₁ hj₂
  set α := a j₁ with hα_def
  set β := b j₂ with hβ_def
  have hαp : α < p := (ha j₁ hj₁).1
  have hβp : β < p := (hb j₂ hj₂).1
  have hαβ : α + β ≤ p - 1 := by
    have := hab j₂ hj₂
    have := hmin₁ j₂ (Finset.mem_range.2 hj₂)
    omega
  have hdα : ∀ j < p, y ^ α ∣ f j := fun j hj =>
    (pow_dvd_pow y (hmin₁ j (Finset.mem_range.2 hj))).trans (ha j hj).2.1
  have hdβ : ∀ j < p, y ^ β ∣ f' j := fun j hj =>
    (pow_dvd_pow y (hmin₂ j (Finset.mem_range.2 hj))).trans (hb j hj).2.1
  -- Newton coefficients and their quotients by `y ^ α`
  have hDα := dvd_newton_of_dvd_values s c r (y ^ α) p hdα
  have hDβ := dvd_newton_of_dvd_values t c' r' (y ^ β) p hdβ
  choose! E hE using hDα
  choose! E' hE' using hDβ
  choose! g hg using hdα
  choose! g' hg' using hdβ
  set G : (A ⧸ Ideal.span {y})[X] := digitPoly α (fun k => π (E k)) with hG
  set G' : (A ⧸ Ideal.span {y})[X] := digitPoly β (fun k => π (E' k)) with hG'
  -- the leading digit of `f j` is `G (j)`
  have keyG : ∀ j < p, π (g j) = G.eval (j : A ⧸ Ideal.span {y}) := fun j hj =>
    digit_eq_eval p hp π y hy ((hπ0 y).2 dvd_rfl) s c r hr α hαp E (fun k hk => hE k hk) j hj
      (g j) (hg j hj)
  have keyG' : ∀ j < p, π (g' j) = G'.eval (j : A ⧸ Ideal.span {y}) := fun j hj =>
    digit_eq_eval p hp π y hy ((hπ0 y).2 dvd_rfl) t c' r' hr' β hβp E' (fun k hk => hE' k hk) j hj
      (g' j) (hg' j hj)
  -- valuation `α` attained iff the digit is nonzero
  have hval : ∀ j < p, (¬ y ^ (α + 1) ∣ f j ↔ G.eval (j : A ⧸ Ideal.span {y}) ≠ 0) := by
    intro j hj
    rw [← keyG j hj, Ne, hπ0, hg j hj, pow_succ]
    exact not_congr (mul_dvd_mul_iff_left (pow_ne_zero α hy))
  have hval' : ∀ j < p, (¬ y ^ (β + 1) ∣ f' j ↔ G'.eval (j : A ⧸ Ideal.span {y}) ≠ 0) := by
    intro j hj
    rw [← keyG' j hj, Ne, hπ0, hg' j hj, pow_succ]
    exact not_congr (mul_dvd_mul_iff_left (pow_ne_zero β hy))
  have hG0 : G ≠ 0 := by
    intro h0
    have := (hval j₁ hj₁).1 (ha j₁ hj₁).2.2
    rw [h0, eval_zero] at this
    exact this rfl
  have hG'0 : G' ≠ 0 := by
    intro h0
    have := (hval' j₂ hj₂).1 (hb j₂ hj₂).2.2
    rw [h0, eval_zero] at this
    exact this rfl
  have hdegGG : (G * G').natDegree ≤ p - 1 :=
    (natDegree_mul_le).trans ((add_le_add (digitPoly_natDegree_le _ _)
      (digitPoly_natDegree_le _ _)).trans hαβ)
  -- a common point where both digits are nonzero
  obtain ⟨j₀, hj₀, hj₀ne⟩ : ∃ j₀ < p, (G * G').eval (j₀ : A ⧸ Ideal.span {y}) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply mul_ne_zero hG0 hG'0
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinj (fun i => hall i i.2) ?_
    rw [Fintype.card_fin]; omega
  rw [eval_mul] at hj₀ne
  have hα₀ : a j₀ = α :=
    exact_pow_dvd_unique (ha j₀ hj₀).2.1 (ha j₀ hj₀).2.2 ⟨g j₀, hg j₀ hj₀⟩
      ((hval j₀ hj₀).2 (left_ne_zero_of_mul hj₀ne))
  have hβ₀ : b j₀ = β :=
    exact_pow_dvd_unique (hb j₀ hj₀).2.1 (hb j₀ hj₀).2.2 ⟨g' j₀, hg' j₀ hj₀⟩
      ((hval' j₀ hj₀).2 (right_ne_zero_of_mul hj₀ne))
  have hαβeq : α + β = p - 1 := by rw [← hα₀, ← hβ₀]; exact hab j₀ hj₀
  have haj : ∀ j < p, a j = α := by
    intro j hj
    have h1 := hab j hj
    have h2 := hmin₁ j (Finset.mem_range.2 hj)
    have h3 := hmin₂ j (Finset.mem_range.2 hj)
    omega
  -- the product of the digits is the constant digit of `ν`
  have hgg : ∀ j < p, g j * g' j = ν := by
    intro j hj
    apply mul_left_cancel₀ (pow_ne_zero (p - 1) hy)
    rw [← hprod' j hj, hg j hj, hg' j hj, ← hαβeq, pow_add]
    ring
  have hπν : π ν ≠ 0 := fun h => hν ((hπ0 ν).1 h)
  have hGG : G * G' = C (π ν) := by
    rw [← sub_eq_zero]
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinj (fun i => ?_) ?_
    · rw [eval_sub, eval_mul, eval_C, ← keyG i i.2, ← keyG' i i.2, ← map_mul, hgg i i.2,
        sub_self]
    · rw [Fintype.card_fin]
      refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
      rw [natDegree_C]
      omega
  have hdeg : G.natDegree = 0 := by
    have := congrArg natDegree hGG
    rw [natDegree_mul hG0 hG'0, natDegree_C] at this
    omega
  refine ⟨α, fun j hj => ⟨⟨g j, hg j hj⟩, by
    have := (ha j hj).2.2; rwa [haj j hj] at this, ?_⟩⟩
  have hres : π (g j) = π (g 0) := by
    rw [keyG j hj, keyG 0 hp0, eq_C_of_natDegree_eq_zero hdeg, eval_C, eval_C]
  have hyd : y ∣ g j - g 0 := (hπ0 _).1 (by rw [map_sub, hres, sub_self])
  show y ^ (α + 1) ∣ f j - f 0
  rw [hg j hj, hg 0 hp0, ← mul_sub, pow_succ]
  exact mul_dvd_mul_left _ hyd

end Core

end CirculantHadamard.RamifiedComparison

end OAI
