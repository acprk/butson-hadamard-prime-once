import OAI.LinearAlgebra.CirculantHadamard.RamifiedComparison.LemmaA
import OAI.LinearAlgebra.CirculantHadamard.RamifiedComparison.Auxiliary

/-!
# Theorem C (case `m = q`): no perfect `p`-phase sequence of length `p q`

Let `p ≠ q` be primes. There is no perfect sequence of length `p q` whose entries are
`p`-th roots of unity.

Proof. View the sequence as `u : C_p × C_q → μ_p ⊂ 𝓞 K`, `K = ℚ(ζ_{pq})`, and let
`h(j, t) = ∑_g u(g) ζ_p^{j g₁} ζ_q^{t g₂}` be its character values; perfectness gives
`h(j, t) h'(j, t) = p q`. For `W = h(0,0) h(j,t) / (h(j,0) h(0,t))`:

* at primes above `p`, Lemma A applied to the rows `t = 0` and `t` shows that `W` is
  integral and `W ≡ 1`; symmetrically at primes above `q` (columns `0` and `j`);
  at all other primes the character values are units;
* `|σ(W)| = 1` for every complex embedding `σ`.

Hence `W` is a root of unity (Kronecker) congruent to `1` modulo primes of residue
characteristics `p` and `q`, so `W = 1`. Summing `h(0,0) h(j,t) = h(j,0) h(0,t)` over `j`
shows that the row `u(0, ·)` has all periodic autocorrelations equal to `0` at nonzero
shifts, while each autocorrelation is `≡ q ≢ 0 (mod ζ_p - 1)`.
-/

namespace OAI

namespace CirculantHadamard.RamifiedComparison

open NumberField IsLocalRing Finset

section Characters

variable {n : ℕ} [hn : Fact n.Prime] {K : Type*} [Field K] {ζ : K}

/-- The additive character `a ↦ ζ ^ a` of `ZMod n`, with values in `𝓞 K`. -/
noncomputable def chi (hζ : IsPrimitiveRoot ζ n) (a : ZMod n) : 𝓞 K :=
  hζ.toInteger ^ a.val

theorem chi_add (hζ : IsPrimitiveRoot ζ n) (a b : ZMod n) :
    chi hζ (a + b) = chi hζ a * chi hζ b :=
  toInteger_pow_val_add hζ a b

theorem chi_zero (hζ : IsPrimitiveRoot ζ n) : chi hζ 0 = 1 := by
  simp [chi]

theorem chi_neg_mul (hζ : IsPrimitiveRoot ζ n) (a : ZMod n) : chi hζ (-a) * chi hζ a = 1 := by
  rw [← chi_add, neg_add_cancel, chi_zero]

theorem chi_pow_eq_one (hζ : IsPrimitiveRoot ζ n) (a : ZMod n) : chi hζ a ^ n = 1 := by
  rw [chi, ← pow_mul, mul_comm, pow_mul, hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]

theorem sub_one_dvd_chi (hζ : IsPrimitiveRoot ζ n) (a : ZMod n) :
    hζ.toInteger - 1 ∣ chi hζ a - 1 := by
  simpa [chi, one_pow] using sub_dvd_pow_sub_pow hζ.toInteger 1 a.val

theorem sum_chi_pow (hζ : IsPrimitiveRoot ζ n) (a : ZMod n) :
    ∑ j ∈ range n, chi hζ a ^ j = if a = 0 then (n : 𝓞 K) else 0 := by
  split_ifs with ha
  · simp [ha, chi_zero]
  · have hne : chi hζ a ≠ 1 := by
      rw [chi]
      refine hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt ?_ (ZMod.val_lt a)
      exact (ZMod.val_ne_zero a).2 ha
    have h := geom_sum_mul (chi hζ a) n
    rw [chi_pow_eq_one, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hne)

end Characters

section Setup

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] {K : Type*} [Field K] [NumberField K]
  {ζp ζq : K} (hζp : IsPrimitiveRoot ζp p) (hζq : IsPrimitiveRoot ζq q)
  (u v : ZMod p × ZMod q → 𝓞 K)

/-- The character values `h(j, t)`. -/
noncomputable def hval (j t : ℕ) : 𝓞 K :=
  ∑ g, u g * chi hζp g.1 ^ j * chi hζq g.2 ^ t

/-- The character values of the "conjugate" array `v` at the inverse characters. -/
noncomputable def hval' (j t : ℕ) : 𝓞 K :=
  ∑ g, v g * chi hζp (-g.1) ^ j * chi hζq (-g.2) ^ t

omit [NumberField K] in
/-- Perfectness gives `h(j, t) h'(j, t) = p q`. -/
theorem hval_mul_hval' (hcorr : ∀ τ, ∑ g, u g * v (g + τ) =
      if τ = 0 then ((p * q : ℕ) : 𝓞 K) else 0) (j t : ℕ) :
    hval hζp hζq u j t * hval' hζp hζq v j t = ((p * q : ℕ) : 𝓞 K) := by
  have hchar : ∀ (g τ : ZMod p × ZMod q),
      (chi hζp g.1 ^ j * chi hζq g.2 ^ t) *
          (chi hζp (-(g + τ).1) ^ j * chi hζq (-(g + τ).2) ^ t) =
        chi hζp (-τ.1) ^ j * chi hζq (-τ.2) ^ t := by
    intro g τ
    have h1 : chi hζp g.1 * chi hζp (-(g + τ).1) = chi hζp (-τ.1) := by
      rw [← chi_add]; congr 1; simp only [Prod.fst_add]; ring
    have h2 : chi hζq g.2 * chi hζq (-(g + τ).2) = chi hζq (-τ.2) := by
      rw [← chi_add]; congr 1; simp only [Prod.snd_add]; ring
    rw [← h1, ← h2]; ring
  calc hval hζp hζq u j t * hval' hζp hζq v j t
      = ∑ g, ∑ τ, u g * v (g + τ) * (chi hζp (-τ.1) ^ j * chi hζq (-τ.2) ^ t) := by
        rw [hval, hval', Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        refine (Fintype.sum_equiv (Equiv.addLeft g) _ _ fun g' => ?_).symm
        simp only [Equiv.coe_addLeft]
        rw [← hchar g g']
        ring
    _ = ∑ τ, (∑ g, u g * v (g + τ)) * (chi hζp (-τ.1) ^ j * chi hζq (-τ.2) ^ t) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Finset.sum_mul]
    _ = ((p * q : ℕ) : 𝓞 K) := by
        rw [Fintype.sum_eq_single 0 fun τ hτ => by simp [hcorr τ, hτ]]
        have h0 : ∑ g, u g * v g = ((p * q : ℕ) : 𝓞 K) := by simpa using hcorr 0
        simp [h0, chi_zero]

omit [NumberField K] in
theorem not_mem_of_liesOver {P : Ideal (𝓞 K)} {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hne : ℓ ≠ ℓ') [P.LiesOver (Ideal.span {(ℓ : ℤ)})] : ((ℓ' : ℕ) : 𝓞 K) ∉ P := by
  intro h
  have : ((ℓ' : ℕ) : ℤ) ∈ P.under ℤ := by simpa using h
  rw [← Ideal.over_def P (Ideal.span {(ℓ : ℤ)}), Ideal.mem_span_singleton, Int.natCast_dvd_natCast,
    Nat.prime_dvd_prime_iff_eq hℓ hℓ'] at this
  exact hne this

omit [NumberField K] in
theorem liesOver_of_mem {P : Ideal (𝓞 K)} [P.IsPrime] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : ((ℓ : ℕ) : 𝓞 K) ∈ P) : P.LiesOver (Ideal.span {(ℓ : ℤ)}) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  refine ⟨(Int.ideal_span_isMaximal_of_prime ℓ).eq_of_le Ideal.IsPrime.ne_top' ?_⟩
  rw [Ideal.span_le, Set.singleton_subset_iff]
  simpa using h

omit [NumberField K] in
/-- Complex conjugation on roots of unity is inversion. -/
theorem conj_eq_of_mul_eq_one (ψ : 𝓞 K →+* ℂ) {x y : 𝓞 K} (hxy : x * y = 1) {n : ℕ}
    (hn : n ≠ 0) (hx : x ^ n = 1) : starRingEnd ℂ (ψ x) = ψ y := by
  have h1 : ‖ψ x‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hx, map_one]) hn
  have h2 : ψ x * ψ y = 1 := by rw [← map_mul, hxy, map_one]
  have h3 : starRingEnd ℂ (ψ x) * ψ x = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
  calc starRingEnd ℂ (ψ x) = starRingEnd ℂ (ψ x) * (ψ x * ψ y) := by rw [h2, mul_one]
    _ = ψ y := by rw [← mul_assoc, h3, one_mul]

omit [NumberField K] in
/-- `|σ(h(j, t))|² = p q` for every complex embedding. -/
theorem norm_sq_hval
    (hcorr : ∀ τ, ∑ g, u g * v (g + τ) = if τ = 0 then ((p * q : ℕ) : 𝓞 K) else 0)
    (hu : ∀ g, ∃ k : ℕ, u g = hζp.toInteger ^ k) (huv : ∀ g, u g * v g = 1)
    (ψ : 𝓞 K →+* ℂ) (j t : ℕ) :
    ‖ψ (hval hζp hζq u j t)‖ ^ 2 = (p * q : ℝ) := by
  have hcu : ∀ g, starRingEnd ℂ (ψ (u g)) = ψ (v g) := fun g => by
    obtain ⟨k, hk⟩ := hu g
    refine conj_eq_of_mul_eq_one ψ (huv g) hp.out.ne_zero ?_
    rw [hk, ← pow_mul, mul_comm, pow_mul, hζp.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
  have hcp : ∀ a : ZMod p, starRingEnd ℂ (ψ (chi hζp a)) = ψ (chi hζp (-a)) := fun a =>
    conj_eq_of_mul_eq_one ψ (by rw [mul_comm]; exact chi_neg_mul hζp a) hp.out.ne_zero
      (chi_pow_eq_one hζp a)
  have hcq : ∀ b : ZMod q, starRingEnd ℂ (ψ (chi hζq b)) = ψ (chi hζq (-b)) := fun b =>
    conj_eq_of_mul_eq_one ψ (by rw [mul_comm]; exact chi_neg_mul hζq b) hq.out.ne_zero
      (chi_pow_eq_one hζq b)
  have hc : starRingEnd ℂ (ψ (hval hζp hζq u j t)) = ψ (hval' hζp hζq v j t) := by
    simp only [hval, hval', map_sum, map_mul, map_pow, hcu, hcp, hcq]
  have h := Complex.mul_conj (ψ (hval hζp hζq u j t))
  rw [hc, ← map_mul, hval_mul_hval' hζp hζq u v hcorr, map_natCast,
    Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h.symm

variable [hK : IsCyclotomicExtension {p * q} ℚ K]

include hK in
/-- Lemma A along the rows: at a prime above `p`, for fixed `t`. -/
theorem pside (hpq : p ≠ q)
    (hcorr : ∀ τ, ∑ g, u g * v (g + τ) = if τ = 0 then ((p * q : ℕ) : 𝓞 K) else 0)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] (t : ℕ) :
    ∃ (α : ℕ) (g : ℕ → Localization.AtPrime P), ∀ j < p,
      IsUnit (g j) ∧
      algebraMap (𝓞 K) (Localization.AtPrime P) (hval hζp hζq u j t) =
        algebraMap (𝓞 K) (Localization.AtPrime P) (hζp.toInteger - 1) ^ α * g j ∧
      g j - g 0 ∈ maximalIdeal (Localization.AtPrime P) := by
  have hpq' : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp.out hq.out).1 h)
  have he : P.ramificationIdx ℤ = p - 1 := by
    have := IsCyclotomicExtension.Rat.ramificationIdx_eq (p * q) K P
      (show p * q = p ^ (0 + 1) * q by ring) hpq'
    rwa [pow_zero, one_mul] at this
  have hy := IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hζp
  have hqP : ((q : ℕ) : 𝓞 K) ∉ P := not_mem_of_liesOver hp.out hq.out hpq
  have e1 : ∀ j, ∑ g ∈ univ, (u g * chi hζq g.2 ^ t) * chi hζp g.1 ^ j = hval hζp hζq u j t :=
    fun j => by rw [hval]; exact Finset.sum_congr rfl fun g _ => by ring
  have e2 : ∀ j, ∑ g ∈ univ, (v g * chi hζq (-g.2) ^ t) * chi hζp (-g.1) ^ j =
      hval' hζp hζq v j t :=
    fun j => by rw [hval']; exact Finset.sum_congr rfl fun g _ => by ring
  obtain ⟨α, g, hg⟩ := lemmaA_localized p P he _ hy univ univ
    (fun g => u g * chi hζq g.2 ^ t) (fun g => chi hζp g.1)
    (fun g => v g * chi hζq (-g.2) ^ t) (fun g => chi hζp (-g.1))
    (fun g _ => sub_one_dvd_chi hζp g.1) (fun g _ => sub_one_dvd_chi hζp (-g.1)) _ hqP
    (fun j _ => by
      rw [e1, e2, hval_mul_hval' hζp hζq u v hcorr, Nat.cast_mul])
  refine ⟨α, g, fun j hj => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hg j hj
  refine ⟨h1, ?_, h3⟩
  rw [← e1]
  exact h2

include hK in
/-- Lemma A along the columns: at a prime above `q`, for fixed `j`. -/
theorem qside (hpq : p ≠ q)
    (hcorr : ∀ τ, ∑ g, u g * v (g + τ) = if τ = 0 then ((p * q : ℕ) : 𝓞 K) else 0)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(q : ℤ)})] (j : ℕ) :
    ∃ (β : ℕ) (g : ℕ → Localization.AtPrime Q), ∀ t < q,
      IsUnit (g t) ∧
      algebraMap (𝓞 K) (Localization.AtPrime Q) (hval hζp hζq u j t) =
        algebraMap (𝓞 K) (Localization.AtPrime Q) (hζq.toInteger - 1) ^ β * g t ∧
      g t - g 0 ∈ maximalIdeal (Localization.AtPrime Q) := by
  have hqp' : ¬ q ∣ p := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).1 h).symm
  have he : Q.ramificationIdx ℤ = q - 1 := by
    have := IsCyclotomicExtension.Rat.ramificationIdx_eq (p * q) K Q
      (show p * q = q ^ (0 + 1) * p by ring) hqp'
    rwa [pow_zero, one_mul] at this
  have hy := IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime q hζq
  have hpQ : ((p : ℕ) : 𝓞 K) ∉ Q := not_mem_of_liesOver hq.out hp.out (Ne.symm hpq)
  have e1 : ∀ t, ∑ g ∈ univ, (u g * chi hζp g.1 ^ j) * chi hζq g.2 ^ t = hval hζp hζq u j t :=
    fun t => rfl
  have e2 : ∀ t, ∑ g ∈ univ, (v g * chi hζp (-g.1) ^ j) * chi hζq (-g.2) ^ t =
      hval' hζp hζq v j t :=
    fun t => rfl
  obtain ⟨β, g, hg⟩ := lemmaA_localized q Q he _ hy univ univ
    (fun g => u g * chi hζp g.1 ^ j) (fun g => chi hζq g.2)
    (fun g => v g * chi hζp (-g.1) ^ j) (fun g => chi hζq (-g.2))
    (fun g _ => sub_one_dvd_chi hζq g.2) (fun g _ => sub_one_dvd_chi hζq (-g.2)) _ hpQ
    (fun t _ => by
      rw [e1, e2, hval_mul_hval' hζp hζq u v hcorr, Nat.cast_mul, mul_comm])
  refine ⟨β, g, fun t ht => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hg t ht
  refine ⟨h1, ?_, h3⟩
  rw [← e1]
  exact h2

include hK in
/-- The ratio `W = h(0,0) h(j,t) / (h(j,0) h(0,t))` at a prime above `p`. -/
theorem ratio_p (hpq : p ≠ q)
    (hcorr : ∀ τ, ∑ g, u g * v (g + τ) = if τ = 0 then ((p * q : ℕ) : 𝓞 K) else 0)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] {j t : ℕ}
    (hj : j < p) :
    ∃ a s : 𝓞 K, s ∉ P ∧
      hval hζp hζq u j 0 * hval hζp hζq u 0 t * a = hval hζp hζq u 0 0 * hval hζp hζq u j t * s ∧
      a - s ∈ P := by
  obtain ⟨α₀, g₀, hg₀⟩ := pside hζp hζq u v hpq hcorr P 0
  obtain ⟨αₜ, gₜ, hgₜ⟩ := pside hζp hζq u v hpq hcorr P t
  have hp0 := hp.out.pos
  refine exists_ratio_rep P _ _ _ _ _ α₀ αₜ (g₀ 0) (g₀ j) (gₜ j) (gₜ 0) (hg₀ j hj).1
    (hgₜ 0 hp0).1 (hg₀ 0 hp0).2.1 (hg₀ j hj).2.1 (hgₜ j hj).2.1 (hgₜ 0 hp0).2.1 ?_ (hgₜ j hj).2.2
  rw [← neg_sub]
  exact (Ideal.neg_mem_iff _).2 (hg₀ j hj).2.2

include hK in
/-- The ratio `W` at a prime above `q`. -/
theorem ratio_q (hpq : p ≠ q)
    (hcorr : ∀ τ, ∑ g, u g * v (g + τ) = if τ = 0 then ((p * q : ℕ) : 𝓞 K) else 0)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(q : ℤ)})] {j t : ℕ}
    (ht : t < q) :
    ∃ a s : 𝓞 K, s ∉ Q ∧
      hval hζp hζq u j 0 * hval hζp hζq u 0 t * a = hval hζp hζq u 0 0 * hval hζp hζq u j t * s ∧
      a - s ∈ Q := by
  obtain ⟨β₀, k₀, hk₀⟩ := qside hζp hζq u v hpq hcorr Q 0
  obtain ⟨βⱼ, kⱼ, hkⱼ⟩ := qside hζp hζq u v hpq hcorr Q j
  have hq0 := hq.out.pos
  obtain ⟨a, s, hs, h1, h2⟩ := exists_ratio_rep Q _ _ _ _ _ β₀ βⱼ (k₀ 0) (k₀ t) (kⱼ t) (kⱼ 0)
    (hk₀ t ht).1 (hkⱼ 0 hq0).1 (hk₀ 0 hq0).2.1 (hk₀ t ht).2.1 (hkⱼ t ht).2.1 (hkⱼ 0 hq0).2.1
    (by rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 (hk₀ t ht).2.2) (hkⱼ t ht).2.2
  exact ⟨a, s, hs, by rw [mul_comm (hval hζp hζq u j 0)]; exact h1, h2⟩

omit hK in
theorem hval_ne_zero
    (hcorr : ∀ τ, ∑ g, u g * v (g + τ) = if τ = 0 then ((p * q : ℕ) : 𝓞 K) else 0)
    (j t : ℕ) : hval hζp hζq u j t ≠ 0 := by
  intro h
  have := hval_mul_hval' hζp hζq u v hcorr j t
  rw [h, zero_mul] at this
  exact (Nat.cast_ne_zero.2 (Nat.mul_ne_zero hp.out.ne_zero hq.out.ne_zero)) this.symm

include hK in
/-- **The key step `W = 1`**: `h(0,0) h(j,t) = h(j,0) h(0,t)`. -/
theorem hval_rel (hpq : p ≠ q)
    (hcorr : ∀ τ, ∑ g, u g * v (g + τ) = if τ = 0 then ((p * q : ℕ) : 𝓞 K) else 0)
    (hu : ∀ g, ∃ k : ℕ, u g = hζp.toInteger ^ k) (huv : ∀ g, u g * v g = 1)
    {j t : ℕ} (hj : j < p) (ht : t < q) :
    hval hζp hζq u 0 0 * hval hζp hζq u j t = hval hζp hζq u j 0 * hval hζp hζq u 0 t := by
  classical
  set A := hval hζp hζq u 0 0 * hval hζp hζq u j t with hA
  set B := hval hζp hζq u j 0 * hval hζp hζq u 0 t with hB
  set ι := algebraMap (𝓞 K) K
  have hι : Function.Injective ι := RingOfIntegers.coe_injective
  have hB0 : B ≠ 0 := mul_ne_zero (hval_ne_zero hζp hζq u v hcorr _ _)
    (hval_ne_zero hζp hζq u v hcorr _ _)
  have hA0 : A ≠ 0 := mul_ne_zero (hval_ne_zero hζp hζq u v hcorr _ _)
    (hval_ne_zero hζp hζq u v hcorr _ _)
  have hιB : ι B ≠ 0 := (map_ne_zero_iff _ hι).2 hB0
  set W : K := ι A / ι B with hW
  -- `W = a / s` from `B a = A s`
  have hdiv : ∀ a s : 𝓞 K, s ≠ 0 → B * a = A * s → W = ι a / ι s := by
    intro a s hs h
    have hιs : ι s ≠ 0 := (map_ne_zero_iff _ hι).2 hs
    rw [hW, div_eq_div_iff hιB hιs, ← map_mul, ← map_mul, mul_comm a B, h]
  have hpq' : (((p * q : ℕ) : 𝓞 K)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Nat.cast_ne_zero.2 (Nat.mul_ne_zero hp.out.ne_zero hq.out.ne_zero))
  -- integrality of `W`
  obtain ⟨w, hw⟩ : ∃ w : 𝓞 K, ι w = W := by
    refine mem_range_of_forall_maximal W fun 𝔓 h𝔓 => ?_
    by_cases hpP : ((p : ℕ) : 𝓞 K) ∈ 𝔓
    · have := liesOver_of_mem hp.out hpP
      obtain ⟨a, s, hs, hrel, -⟩ := ratio_p hζp hζq u v hpq hcorr 𝔓 hj (t := t)
      exact ⟨a, s, hs, hdiv a s (fun h => hs (h ▸ 𝔓.zero_mem)) hrel⟩
    by_cases hqP : ((q : ℕ) : 𝓞 K) ∈ 𝔓
    · have := liesOver_of_mem hq.out hqP
      obtain ⟨a, s, hs, hrel, -⟩ := ratio_q hζp hζq u v hpq hcorr 𝔓 ht (j := j)
      exact ⟨a, s, hs, hdiv a s (fun h => hs (h ▸ 𝔓.zero_mem)) hrel⟩
    · refine ⟨A * (hval' hζp hζq v j 0 * hval' hζp hζq v 0 t), ((p * q : ℕ) : 𝓞 K) ^ 2,
        fun h => ?_, hdiv _ _ hpq' ?_⟩
      · have h' := h𝔓.isPrime.mem_of_pow_mem 2 h
        rw [Nat.cast_mul] at h'
        rcases h𝔓.isPrime.mem_or_mem h' with h'' | h''
        · exact hpP h''
        · exact hqP h''
      · rw [hB, pow_two]
        have e1 := hval_mul_hval' hζp hζq u v hcorr j 0
        have e2 := hval_mul_hval' hζp hζq u v hcorr 0 t
        calc hval hζp hζq u j 0 * hval hζp hζq u 0 t *
              (A * (hval' hζp hζq v j 0 * hval' hζp hζq v 0 t))
            = A * ((hval hζp hζq u j 0 * hval' hζp hζq v j 0) *
                (hval hζp hζq u 0 t * hval' hζp hζq v 0 t)) := by ring
          _ = _ := by rw [e1, e2]
  -- `|σ W| = 1` for every embedding
  have hnorm : ∀ φ : K →+* ℂ, ‖φ W‖ = 1 := by
    intro φ
    set ψ := φ.comp ι
    have hn := fun j t => norm_sq_hval hζp hζq u v hcorr hu huv ψ j t
    have hpos : (0 : ℝ) < p * q := by
      have := hp.out.pos; have := hq.out.pos; positivity
    have heq : ∀ j t j' t', ‖ψ (hval hζp hζq u j t)‖ = ‖ψ (hval hζp hζq u j' t')‖ :=
      fun j t j' t' => (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
        ((hn j t).trans (hn j' t').symm)
    have hne : ‖ψ (hval hζp hζq u 0 0)‖ ≠ 0 := by
      intro h; have := hn 0 0; rw [h, zero_pow two_ne_zero] at this; linarith
    rw [hW, map_div₀]
    change ‖ψ A / ψ B‖ = 1
    rw [hA, hB, map_mul, map_mul, norm_div, norm_mul, norm_mul, heq j t 0 0, heq j 0 0 0,
      heq 0 t 0 0, div_self (mul_ne_zero hne hne)]
  have hint : IsIntegral ℤ W := by rw [← hw]; exact RingOfIntegers.isIntegral_coe w
  obtain ⟨n, hn, hWn⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ hint hnorm
  have hwn : w ^ n = 1 := hι (by rw [map_pow, hw, hWn, map_one])
  -- primes above `p` and `q`
  have : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have : (Ideal.span {(q : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime q
  obtain ⟨P, hPmax, hPo⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)})
  obtain ⟨Q, hQmax, hQo⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) (Ideal.span {(q : ℤ)})
  have hsub : ∀ (𝔓 : Ideal (𝓞 K)) [𝔓.IsPrime] (a s : 𝓞 K), s ∉ 𝔓 → B * a = A * s →
      a - s ∈ 𝔓 → w - 1 ∈ 𝔓 := by
    intro 𝔓 _ a s hs hrel hmem
    have hs0 : s ≠ 0 := fun h => hs (h ▸ 𝔓.zero_mem)
    have hws : w * s = a := by
      apply hι
      have := hdiv a s hs0 hrel
      rw [← hw] at this
      rw [map_mul, this, div_mul_cancel₀ _ ((map_ne_zero_iff _ hι).2 hs0)]
    have : (w - 1) * s ∈ 𝔓 := by rw [sub_mul, hws, one_mul]; exact hmem
    exact ((inferInstance : 𝔓.IsPrime).mem_or_mem this).resolve_right hs
  have hwP : w - 1 ∈ P := by
    obtain ⟨a, s, hs, hrel, hmem⟩ := ratio_p hζp hζq u v hpq hcorr P hj (t := t)
    exact hsub P a s hs hrel hmem
  have hwQ : w - 1 ∈ Q := by
    obtain ⟨a, s, hs, hrel, hmem⟩ := ratio_q hζp hζq u v hpq hcorr Q ht (j := j)
    exact hsub Q a s hs hrel hmem
  have hw1 : w = 1 := eq_one_of_pow_eq_one_of_sub_one_mem hn hwn P Q hpq hwP hwQ
    (fun ℓ hℓ hmem => by
      by_contra hne
      exact not_mem_of_liesOver hp.out hℓ (Ne.symm hne) hmem)
    (fun ℓ hℓ hmem => by
      by_contra hne
      exact not_mem_of_liesOver hq.out hℓ (Ne.symm hne) hmem)
  have : ι A = ι B := by
    have h1 : W = 1 := by rw [← hw, hw1, map_one]
    rw [hW, div_eq_one_iff_eq hιB] at h1
    exact h1
  exact hι this

omit [NumberField K] in
/-- Orthogonality along the rows: `∑_j h(j, t) = p ρ(t)`, `ρ(t) = ∑_b u(0,b) ζ_q^{t b}`. -/
theorem sum_hval (t : ℕ) :
    ∑ j ∈ range p, hval hζp hζq u j t =
      (p : 𝓞 K) * ∑ b, u (0, b) * chi hζq b ^ t := by
  unfold hval
  rw [Finset.sum_comm]
  have : ∀ g : ZMod p × ZMod q, ∑ j ∈ range p, u g * chi hζp g.1 ^ j * chi hζq g.2 ^ t =
      u g * chi hζq g.2 ^ t * (if g.1 = 0 then (p : 𝓞 K) else 0) := fun g => by
    rw [← sum_chi_pow hζp g.1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [this]
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single 0 fun a ha => by simp [ha], Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by simp; ring

omit [NumberField K] in
theorem sum_hval' (t : ℕ) :
    ∑ j ∈ range p, hval' hζp hζq v j t =
      (p : 𝓞 K) * ∑ b, v (0, b) * chi hζq (-b) ^ t := by
  unfold hval'
  rw [Finset.sum_comm]
  have : ∀ g : ZMod p × ZMod q, ∑ j ∈ range p, v g * chi hζp (-g.1) ^ j * chi hζq (-g.2) ^ t =
      v g * chi hζq (-g.2) ^ t * (if g.1 = 0 then (p : 𝓞 K) else 0) := fun g => by
    have e : (if g.1 = 0 then (p : 𝓞 K) else 0) = if -g.1 = 0 then (p : 𝓞 K) else 0 := by
      simp [neg_eq_zero]
    rw [e, ← sum_chi_pow hζp (-g.1), Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [this]
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single 0 fun a ha => by simp [ha], Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by simp; ring

omit [NumberField K] in
/-- `ρ(t) ρ'(t) = ∑_s ζ_q^{-t s} A(s)` with `A(s) = ∑_b u(0,b) v(0,b+s)`. -/
theorem rho_mul_rho' (t : ℕ) :
    (∑ b, u (0, b) * chi hζq b ^ t) * (∑ b, v (0, b) * chi hζq (-b) ^ t) =
      ∑ s, chi hζq (-s) ^ t * ∑ b, u (0, b) * v (0, b + s) := by
  rw [Finset.sum_mul_sum]
  calc ∑ b, ∑ b', u (0, b) * chi hζq b ^ t * (v (0, b') * chi hζq (-b') ^ t)
      = ∑ b, ∑ s, u (0, b) * v (0, b + s) * chi hζq (-s) ^ t := by
        refine Finset.sum_congr rfl fun b _ => ?_
        refine (Fintype.sum_equiv (Equiv.addLeft b) _ _ fun s => ?_).symm
        simp only [Equiv.coe_addLeft]
        have h1 : chi hζq b * chi hζq (-(b + s)) = chi hζq (-s) := by
          rw [← chi_add]; congr 1; ring
        rw [← h1]; ring
    _ = ∑ s, chi hζq (-s) ^ t * ∑ b, u (0, b) * v (0, b + s) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring

include hK hζq in
/-- **Theorem C, ring-theoretic form.** -/
theorem theoremC_core (hpq : p ≠ q)
    (hcorr : ∀ τ, ∑ g, u g * v (g + τ) = if τ = 0 then ((p * q : ℕ) : 𝓞 K) else 0)
    (hu : ∀ g, ∃ k : ℕ, u g = hζp.toInteger ^ k) (hv : ∀ g, ∃ k : ℕ, v g = hζp.toInteger ^ k)
    (huv : ∀ g, u g * v g = 1) : False := by
  classical
  set N : 𝓞 K := ((p * q : ℕ) : 𝓞 K) with hN
  have hN0 : N ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_ne_zero hp.out.ne_zero hq.out.ne_zero)
  have hp0 : (p : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hq0 : (q : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hq.out.ne_zero
  have hhh := hval_mul_hval' hζp hζq u v hcorr
  have hrel := fun {j t : ℕ} (hj : j < p) (ht : t < q) =>
    hval_rel hζp hζq u v hpq hcorr hu huv hj ht
  -- the same relation for `h'`
  have hrel' : ∀ {j t : ℕ}, j < p → t < q →
      hval' hζp hζq v 0 0 * hval' hζp hζq v j t = hval' hζp hζq v j 0 * hval' hζp hζq v 0 t := by
    intro j t hj ht
    have hX : hval hζp hζq u 0 0 * hval hζp hζq u j t ≠ 0 :=
      mul_ne_zero (hval_ne_zero hζp hζq u v hcorr _ _) (hval_ne_zero hζp hζq u v hcorr _ _)
    apply mul_left_cancel₀ hX
    calc hval hζp hζq u 0 0 * hval hζp hζq u j t *
          (hval' hζp hζq v 0 0 * hval' hζp hζq v j t)
        = (hval hζp hζq u 0 0 * hval' hζp hζq v 0 0) *
            (hval hζp hζq u j t * hval' hζp hζq v j t) := by ring
      _ = (hval hζp hζq u j 0 * hval' hζp hζq v j 0) *
            (hval hζp hζq u 0 t * hval' hζp hζq v 0 t) := by rw [hhh, hhh, hhh, hhh]
      _ = hval hζp hζq u 0 0 * hval hζp hζq u j t *
            (hval' hζp hζq v j 0 * hval' hζp hζq v 0 t) := by rw [hrel hj ht]; ring
  set ρ : ℕ → 𝓞 K := fun t => ∑ b, u (0, b) * chi hζq b ^ t with hρ
  set ρ' : ℕ → 𝓞 K := fun t => ∑ b, v (0, b) * chi hζq (-b) ^ t with hρ'
  -- summing the relations over `j`
  have hsum : ∀ t < q, hval hζp hζq u 0 0 * ((p : 𝓞 K) * ρ t) =
      hval hζp hζq u 0 t * ((p : 𝓞 K) * ρ 0) := by
    intro t ht
    rw [hρ]; dsimp only
    rw [← sum_hval hζp hζq u t, ← sum_hval hζp hζq u 0, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj => by
      rw [hrel (Finset.mem_range.1 hj) ht]; ring
  have hsum' : ∀ t < q, hval' hζp hζq v 0 0 * ((p : 𝓞 K) * ρ' t) =
      hval' hζp hζq v 0 t * ((p : 𝓞 K) * ρ' 0) := by
    intro t ht
    rw [hρ']; dsimp only
    rw [← sum_hval' hζp hζq v t, ← sum_hval' hζp hζq v 0, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj => by
      rw [hrel' (Finset.mem_range.1 hj) ht]; ring
  have hconst : ∀ t < q, ρ t * ρ' t = ρ 0 * ρ' 0 := by
    intro t ht
    have h := congrArg₂ (· * ·) (hsum t ht) (hsum' t ht)
    have hpN : (p : 𝓞 K) * (p : 𝓞 K) * N ≠ 0 := mul_ne_zero (mul_ne_zero hp0 hp0) hN0
    apply mul_left_cancel₀ hpN
    calc (p : 𝓞 K) * p * N * (ρ t * ρ' t)
        = hval hζp hζq u 0 0 * hval' hζp hζq v 0 0 * (p * p) * (ρ t * ρ' t) := by
          rw [hhh, ← hN]; ring
      _ = hval hζp hζq u 0 0 * (p * ρ t) * (hval' hζp hζq v 0 0 * (p * ρ' t)) := by ring
      _ = hval hζp hζq u 0 t * (p * ρ 0) * (hval' hζp hζq v 0 t * (p * ρ' 0)) := h
      _ = hval hζp hζq u 0 t * hval' hζp hζq v 0 t * (p * p) * (ρ 0 * ρ' 0) := by ring
      _ = (p : 𝓞 K) * p * N * (ρ 0 * ρ' 0) := by rw [hhh, ← hN]; ring
  -- Fourier inversion at the shift `1`
  set A : ZMod q → 𝓞 K := fun s => ∑ b, u (0, b) * v (0, b + s) with hA
  have h1ne : (1 : ZMod q) ≠ 0 := one_ne_zero
  have hF : ∑ t ∈ range q, chi hζq 1 ^ t * (ρ t * ρ' t) = (q : 𝓞 K) * A 1 := by
    calc ∑ t ∈ range q, chi hζq 1 ^ t * (ρ t * ρ' t)
        = ∑ t ∈ range q, ∑ s, A s * chi hζq (1 - s) ^ t := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hρ, hρ']; dsimp only
          rw [rho_mul_rho', Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          have : chi hζq 1 * chi hζq (-s) = chi hζq (1 - s) := by rw [← chi_add, sub_eq_add_neg]
          rw [← this, mul_pow]; ring
      _ = ∑ s, A s * ∑ t ∈ range q, chi hζq (1 - s) ^ t := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun s _ => by rw [Finset.mul_sum]
      _ = (q : 𝓞 K) * A 1 := by
          simp_rw [sum_chi_pow hζq, sub_eq_zero]
          rw [Fintype.sum_eq_single 1 fun s hs => by simp [Ne.symm hs]]
          simp [mul_comm]
  have hF' : ∑ t ∈ range q, chi hζq 1 ^ t * (ρ t * ρ' t) = 0 := by
    rw [Finset.sum_congr rfl fun t ht => by rw [hconst t (Finset.mem_range.1 ht)],
      ← Finset.sum_mul, sum_chi_pow hζq]
    simp [h1ne]
  have hA1 : A 1 = 0 := by
    have := hF.symm.trans hF'
    exact (mul_eq_zero.1 this).resolve_left hq0
  -- but `A 1 ≡ q (mod ζ_p - 1)`
  have hdvd : hζp.toInteger - 1 ∣ A 1 - q := by
    have : A 1 - q = ∑ b : ZMod q, (u (0, b) * v (0, b + 1) - 1) := by
      rw [Finset.sum_sub_distrib, hA]
      simp
    rw [this]
    refine Finset.dvd_sum fun b _ => ?_
    obtain ⟨k, hk⟩ := hu (0, b)
    obtain ⟨k', hk'⟩ := hv (0, b + 1)
    rw [hk, hk', ← pow_add]
    simpa [one_pow] using sub_dvd_pow_sub_pow hζp.toInteger 1 (k + k')
  rw [hA1, zero_sub, dvd_neg] at hdvd
  -- a prime above `p` contains `ζ_p - 1`, hence `q`
  have : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨P, hPmax, hPo⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)})
  have hpP : ((p : ℕ) : 𝓞 K) ∈ P := by
    have : (p : ℤ) ∈ P.under ℤ := by
      rw [← Ideal.over_def P (Ideal.span {(p : ℤ)})]
      exact Ideal.subset_span rfl
    simpa using this
  obtain ⟨w, hw⟩ := IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hζp
  have hyP : hζp.toInteger - 1 ∈ P := by
    rw [← hw] at hpP
    rcases hPmax.isPrime.mem_or_mem hpP with h | h
    · exact hPmax.isPrime.mem_of_pow_mem _ h
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ h w.isUnit) hPmax.ne_top
  have hqP : ((q : ℕ) : 𝓞 K) ∈ P := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc]
    exact P.mul_mem_right _ hyP
  exact not_mem_of_liesOver hp.out hq.out hpq hqP

end Setup

end CirculantHadamard.RamifiedComparison

end OAI

namespace OAI

namespace CirculantHadamard.RamifiedComparison

open NumberField Finset

theorem not_exists_perfect_prime_phase_aux (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (K : Type*) [Field K] [NumberField K] [NeZero (p * q)]
    [IsCyclotomicExtension {p * q} ℚ K] :
    ¬ ∃ a : ZMod (p * q) → ℂ,
      (∀ j, a j ^ p = 1) ∧
      ∀ τ : ZMod (p * q), τ ≠ 0 →
        ∑ j, a j * (starRingEnd ℂ) (a (j + τ)) = 0 := by
  classical
  rintro ⟨a, ha, hauto⟩
  let η := IsCyclotomicExtension.zeta (p * q) ℚ K
  have hη : IsPrimitiveRoot η (p * q) := IsCyclotomicExtension.zeta_spec (p * q) ℚ K
  have hpq0 : 0 < p * q := Nat.pos_of_ne_zero (NeZero.ne _)
  have hζp : IsPrimitiveRoot (η ^ q) p := hη.pow hpq0 (mul_comm p q)
  have hζq : IsPrimitiveRoot (η ^ p) q := hη.pow hpq0 rfl
  let φ₀ : K →+* ℂ := (IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom
  let Φ : 𝓞 K →+* ℂ := φ₀.comp (algebraMap (𝓞 K) K)
  have hΦinj : Function.Injective Φ :=
    φ₀.injective.comp RingOfIntegers.coe_injective
  set zp := hζp.toInteger
  have hω : IsPrimitiveRoot (Φ zp) p := by
    have : Φ zp = φ₀ (η ^ q) := rfl
    rw [this]
    exact hζp.map_of_injective φ₀.injective
  have hcop : p.Coprime q := (Nat.coprime_primes hp.out hq.out).2 hpq
  let e : ZMod (p * q) ≃+* ZMod p × ZMod q := ZMod.chineseRemainder hcop
  have hk : ∀ x, ∃ i < p, Φ zp ^ i = a x := fun x => hω.eq_pow_of_pow_eq_one (ha x)
  choose k _ hk using hk
  let u : ZMod p × ZMod q → 𝓞 K := fun g => zp ^ k (e.symm g)
  let v : ZMod p × ZMod q → 𝓞 K := fun g => zp ^ ((p - 1) * k (e.symm g))
  have hzp : zp ^ p = 1 := hζp.toInteger_isPrimitiveRoot.pow_eq_one
  have huv : ∀ g, u g * v g = 1 := fun g => by
    simp only [u, v]
    rw [← pow_add, show k (e.symm g) + (p - 1) * k (e.symm g) = p * k (e.symm g) by
      have := hp.out.one_le
      zify [this]; ring, pow_mul, hzp, one_pow]
  have hΦu : ∀ g, Φ (u g) = a (e.symm g) := fun g => by
    simp only [u, map_pow]; exact hk _
  have hΦv : ∀ g, Φ (v g) = (starRingEnd ℂ) (a (e.symm g)) := fun g => by
    rw [← hΦu, conj_eq_of_mul_eq_one Φ (huv g) hp.out.ne_zero (by
      simp only [u]; rw [← pow_mul, mul_comm (k _) p, pow_mul, hzp, one_pow])]
  have hcorr : ∀ τ, ∑ g, u g * v (g + τ) = if τ = 0 then ((p * q : ℕ) : 𝓞 K) else 0 := by
    intro τ
    split_ifs with hτ
    · subst hτ
      simp only [add_zero, huv, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        ZMod.card, nsmul_eq_mul, mul_one, Nat.cast_mul]
    · apply hΦinj
      rw [map_sum, map_zero]
      simp only [map_mul, hΦu, hΦv, map_add e.symm]
      have hτ' : e.symm τ ≠ 0 := by
        intro h; apply hτ
        rw [← e.apply_symm_apply τ, h, map_zero]
      rw [← hauto (e.symm τ) hτ']
      exact Fintype.sum_equiv e.symm.toEquiv _ _ fun g => rfl
  exact theoremC_core hζp hζq u v hpq hcorr (fun g => ⟨_, rfl⟩) (fun g => ⟨_, rfl⟩) huv

/-- **Theorem C (`m = q`).** For primes `p ≠ q` there is no perfect sequence of length
`p q` whose entries are `p`-th roots of unity: no `a : ZMod (p q) → ℂ` with `a j ^ p = 1`
has all nontrivial periodic autocorrelations equal to zero. -/
theorem not_exists_perfect_prime_phase (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) :
    ¬ ∃ a : ZMod (p * q) → ℂ,
      (∀ j, a j ^ p = 1) ∧
      ∀ τ : ZMod (p * q), τ ≠ 0 →
        ∑ j, a j * (starRingEnd ℂ) (a (j + τ)) = 0 := by
  have : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.out.ne_zero hq.out.ne_zero⟩
  have hcyc : IsCyclotomicExtension {p * q} ℚ (CyclotomicField (p * q) ℚ) := by
    convert (inferInstance : @IsCyclotomicExtension {p * q} ℚ (CyclotomicField (p * q) ℚ) _ _
      (CyclotomicField.algebra (p * q) ℚ))
    exact Subsingleton.elim _ _
  exact not_exists_perfect_prime_phase_aux p q hpq (CyclotomicField (p * q) ℚ)

end CirculantHadamard.RamifiedComparison

end OAI
