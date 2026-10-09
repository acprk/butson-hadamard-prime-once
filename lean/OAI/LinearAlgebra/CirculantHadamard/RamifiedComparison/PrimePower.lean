import OAI.LinearAlgebra.CirculantHadamard.RamifiedComparison.TheoremC
import OAI.LinearAlgebra.CirculantHadamard.AlternatingLocalization
import OAI.LinearAlgebra.CirculantHadamard.CyclotomicLocalBase

/-!
# Theorem C for `m = q ^ e`: no perfect `p`-phase sequence of length `p q ^ e`

Same strategy as `TheoremC.lean` (the case `e = 1`), with the group `C_p × C_N`,
`N = q ^ e`, and characters of `C_N` of order dividing `q`:

* at primes above `p` the comparison is Lemma A (`lemmaA_localized`), applied for each
  character of `C_N` (the norm `p N` has `p`-adic valuation one);
* at primes above `q` the comparison is the unramified local character comparison of the
  circulant Hadamard formalization (`actual_local_character_association`), applied to the
  partial evaluations in `ℤ[ζ_p][C_N]` (the norm is `q ^ e` times the unit `p`);
* Kronecker's theorem and the two congruences give `W = 1`, and Fourier inversion over the
  characters of order `q` gives the contradiction `q ^ (2e) ≡ 0 (mod ζ_p - 1)`.
-/

namespace OAI

namespace CirculantHadamard.RamifiedComparison

open NumberField IsLocalRing Finset

section CharactersN

variable {q : ℕ} [NeZero q] {K : Type*} [Field K] {ζ : K}

/-- The character `b ↦ ζ ^ b` of `ZMod N` for a `q`-th root of unity `ζ`, `q ∣ N`. -/
noncomputable def chiN (hζ : IsPrimitiveRoot ζ q) (N : ℕ) (b : ZMod N) : 𝓞 K :=
  hζ.toInteger ^ b.val

theorem toInteger_pow_mod_of_dvd (hζ : IsPrimitiveRoot ζ q) {N : ℕ} (hqN : q ∣ N) (x : ℕ) :
    hζ.toInteger ^ x = hζ.toInteger ^ (x % N) := by
  obtain ⟨c, rfl⟩ := hqN
  conv_lhs => rw [← Nat.div_add_mod x (q * c), pow_add, pow_mul, pow_mul,
    hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow, one_pow, one_mul]

theorem chiN_add (hζ : IsPrimitiveRoot ζ q) {N : ℕ} [NeZero N] (hqN : q ∣ N) (a b : ZMod N) :
    chiN hζ N (a + b) = chiN hζ N a * chiN hζ N b := by
  rw [chiN, chiN, chiN, ← pow_add, toInteger_pow_mod_of_dvd hζ hqN (a.val + b.val), ZMod.val_add]

theorem chiN_zero (hζ : IsPrimitiveRoot ζ q) (N : ℕ) : chiN hζ N 0 = 1 := by
  simp [chiN]

theorem chiN_neg_mul (hζ : IsPrimitiveRoot ζ q) {N : ℕ} [NeZero N] (hqN : q ∣ N) (b : ZMod N) :
    chiN hζ N (-b) * chiN hζ N b = 1 := by
  rw [← chiN_add hζ hqN, neg_add_cancel, chiN_zero]

theorem chiN_pow_eq_one (hζ : IsPrimitiveRoot ζ q) (N : ℕ) (b : ZMod N) : chiN hζ N b ^ q = 1 := by
  rw [chiN, ← pow_mul, mul_comm, pow_mul, hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]

theorem sub_one_dvd_chiN (hζ : IsPrimitiveRoot ζ q) (N : ℕ) (b : ZMod N) :
    hζ.toInteger - 1 ∣ chiN hζ N b - 1 := by
  simpa [chiN, one_pow] using sub_dvd_pow_sub_pow hζ.toInteger 1 b.val

/-- Orthogonality in `t < q`. -/
theorem sum_chiN_pow (hζ : IsPrimitiveRoot ζ q) (N : ℕ) (b : ZMod N) :
    ∑ t ∈ range q, chiN hζ N b ^ t = if q ∣ b.val then (q : 𝓞 K) else 0 := by
  split_ifs with hb
  · have : chiN hζ N b = 1 := by
      obtain ⟨c, hc⟩ := hb
      rw [chiN, hc, pow_mul, hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
    simp [this]
  · have hne : chiN hζ N b ≠ 1 := fun h =>
      hb ((hζ.toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd _).1 h)
    have h := geom_sum_mul (chiN hζ N b) q
    rw [chiN_pow_eq_one, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hne)

/-- Orthogonality in `b ∈ ZMod N`. -/
theorem sum_chiN_pow_univ (hζ : IsPrimitiveRoot ζ q) {N : ℕ} [NeZero N] (hqN : q ∣ N) (t : ℕ) :
    ∑ b : ZMod N, chiN hζ N b ^ t = if q ∣ t then (N : 𝓞 K) else 0 := by
  have hreindex : ∑ b : ZMod N, chiN hζ N b ^ t = ∑ i ∈ range N, (hζ.toInteger ^ t) ^ i := by
    refine Finset.sum_nbij' (fun b : ZMod N => b.val) (fun i => (i : ZMod N))
      (fun b _ => Finset.mem_range.2 (ZMod.val_lt b)) (fun _ _ => Finset.mem_univ _)
      (fun b _ => ZMod.natCast_zmod_val b)
      (fun i hi => ZMod.val_cast_of_lt (Finset.mem_range.1 hi)) fun b _ => ?_
    rw [chiN, ← pow_mul, ← pow_mul, mul_comm]
  rw [hreindex]
  split_ifs with ht
  · have : hζ.toInteger ^ t = 1 := by
      obtain ⟨c, hc⟩ := ht
      rw [hc, pow_mul, hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
    simp [this]
  · have hne : hζ.toInteger ^ t ≠ 1 := fun h =>
      ht ((hζ.toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd _).1 h)
    have h := geom_sum_mul (hζ.toInteger ^ t) N
    have hN : (hζ.toInteger ^ t) ^ N = 1 := by
      obtain ⟨c, hc⟩ := hqN
      rw [hc, ← pow_mul, mul_comm, mul_assoc, pow_mul,
        hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
    rw [hN, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hne)

end CharactersN

section Generic

/-- From a unit ratio `X ≡ 1` in `R_𝔓` to a global representation `a / s`. -/
theorem exists_rep_of_unit {R : Type*} [CommRing R] [IsDomain R] (𝔓 : Ideal R) [𝔓.IsPrime]
    (A B : R) (X : Localization.AtPrime 𝔓)
    (hX : algebraMap R (Localization.AtPrime 𝔓) B * X = algebraMap R (Localization.AtPrime 𝔓) A)
    (hX1 : X - 1 ∈ maximalIdeal (Localization.AtPrime 𝔓)) :
    ∃ a s : R, s ∉ 𝔓 ∧ B * a = A * s ∧ a - s ∈ 𝔓 := by
  set φ := algebraMap R (Localization.AtPrime 𝔓)
  obtain ⟨⟨a, ⟨s, hs⟩⟩, hXa⟩ := IsLocalization.mk'_surjective 𝔓.primeCompl X
  have hXs : X * φ s = φ a := by
    rw [← hXa]; exact IsLocalization.mk'_spec (Localization.AtPrime 𝔓) a ⟨s, hs⟩
  have hinj : Function.Injective φ :=
    IsLocalization.injective (Localization.AtPrime 𝔓) 𝔓.primeCompl_le_nonZeroDivisors
  refine ⟨a, s, hs, hinj ?_, ?_⟩
  · rw [map_mul, ← hXs, ← mul_assoc, hX, map_mul]
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔓) 𝔓]
    have : φ (a - s) = (X - 1) * φ s := by rw [map_sub, ← hXs]; ring
    rw [this]
    exact Ideal.mul_mem_right _ _ hX1

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- A ring embedding of the complex cyclotomic order `ℤ[Φ z]` back into `𝓞 K`. -/
theorem exists_order_hom (Φ : 𝓞 K →+* ℂ) (hΦ : Function.Injective Φ) (z : 𝓞 K) :
    ∃ κ : CyclotomicLocalBase.Order (Φ z) →+* 𝓞 K, Function.Injective κ ∧
      κ (CyclotomicLocalBase.generator (Φ z)) = z := by
  let S0 : Subalgebra ℤ (𝓞 K) := Algebra.adjoin ℤ {z}
  let Ψ : 𝓞 K →ₐ[ℤ] ℂ := Φ.toIntAlgHom
  have hmap : S0.map Ψ = CyclotomicLocalBase.Order (Φ z) := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    rfl
  let E : S0 ≃ₐ[ℤ] CyclotomicLocalBase.Order (Φ z) :=
    (Subalgebra.equivMapOfInjective S0 Ψ hΦ).trans (Subalgebra.equivOfEq _ _ hmap)
  refine ⟨S0.val.toRingHom.comp E.symm.toRingHom,
    Subtype.val_injective.comp E.symm.injective, ?_⟩
  have hz : E ⟨z, Algebra.subset_adjoin (Set.mem_singleton z)⟩ =
      CyclotomicLocalBase.generator (Φ z) := Subtype.ext rfl
  change ((E.symm (CyclotomicLocalBase.generator (Φ z)) : S0) : 𝓞 K) = z
  rw [← hz, AlgEquiv.symm_apply_apply]

end Generic

section SetupN

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] {K : Type*} [Field K] [NumberField K]
  {ζp ζq : K} (hζp : IsPrimitiveRoot ζp p) (hζq : IsPrimitiveRoot ζq q)
  {N : ℕ} [NeZero N] (u v : ZMod p × ZMod N → 𝓞 K)

/-- The character values `h(j, t)` (characters of `C_N` of order dividing `q`). -/
noncomputable def hvalN (j t : ℕ) : 𝓞 K :=
  ∑ g, u g * chi hζp g.1 ^ j * chiN hζq N g.2 ^ t

/-- The character values of the "conjugate" array `v` at the inverse characters. -/
noncomputable def hvalN' (j t : ℕ) : 𝓞 K :=
  ∑ g, v g * chi hζp (-g.1) ^ j * chiN hζq N (-g.2) ^ t

omit [NumberField K] in
/-- Perfectness gives `h(j, t) h'(j, t) = p q`. -/
theorem hvalN_mul_hvalN' (hqN : q ∣ N) (hcorr : ∀ τ, ∑ g, u g * v (g + τ) =
      if τ = 0 then ((p * N : ℕ) : 𝓞 K) else 0) (j t : ℕ) :
    hvalN hζp hζq u j t * hvalN' hζp hζq v j t = ((p * N : ℕ) : 𝓞 K) := by
  have hchar : ∀ (g τ : ZMod p × ZMod N),
      (chi hζp g.1 ^ j * chiN hζq N g.2 ^ t) *
          (chi hζp (-(g + τ).1) ^ j * chiN hζq N (-(g + τ).2) ^ t) =
        chi hζp (-τ.1) ^ j * chiN hζq N (-τ.2) ^ t := by
    intro g τ
    have h1 : chi hζp g.1 * chi hζp (-(g + τ).1) = chi hζp (-τ.1) := by
      rw [← chi_add]; congr 1; simp only [Prod.fst_add]; ring
    have h2 : chiN hζq N g.2 * chiN hζq N (-(g + τ).2) = chiN hζq N (-τ.2) := by
      rw [← chiN_add hζq hqN]; congr 1; simp only [Prod.snd_add]; ring
    rw [← h1, ← h2]; ring
  calc hvalN hζp hζq u j t * hvalN' hζp hζq v j t
      = ∑ g, ∑ τ, u g * v (g + τ) * (chi hζp (-τ.1) ^ j * chiN hζq N (-τ.2) ^ t) := by
        rw [hvalN, hvalN', Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        refine (Fintype.sum_equiv (Equiv.addLeft g) _ _ fun g' => ?_).symm
        simp only [Equiv.coe_addLeft]
        rw [← hchar g g']
        ring
    _ = ∑ τ, (∑ g, u g * v (g + τ)) * (chi hζp (-τ.1) ^ j * chiN hζq N (-τ.2) ^ t) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Finset.sum_mul]
    _ = ((p * N : ℕ) : 𝓞 K) := by
        rw [Fintype.sum_eq_single 0 fun τ hτ => by simp [hcorr τ, hτ]]
        have h0 : ∑ g, u g * v g = ((p * N : ℕ) : 𝓞 K) := by simpa using hcorr 0
        simp [h0, chi_zero, chiN_zero]

omit [NumberField K] in
/-- `|σ(h(j, t))|² = p q` for every complex embedding. -/
theorem norm_sq_hvalN
    (hqN : q ∣ N) (hcorr : ∀ τ, ∑ g, u g * v (g + τ) = if τ = 0 then ((p * N : ℕ) : 𝓞 K) else 0)
    (hu : ∀ g, ∃ k : ℕ, u g = hζp.toInteger ^ k) (huv : ∀ g, u g * v g = 1)
    (ψ : 𝓞 K →+* ℂ) (j t : ℕ) :
    ‖ψ (hvalN hζp hζq u j t)‖ ^ 2 = (p * N : ℝ) := by
  have hcu : ∀ g, starRingEnd ℂ (ψ (u g)) = ψ (v g) := fun g => by
    obtain ⟨k, hk⟩ := hu g
    refine conj_eq_of_mul_eq_one ψ (huv g) hp.out.ne_zero ?_
    rw [hk, ← pow_mul, mul_comm, pow_mul, hζp.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
  have hcp : ∀ a : ZMod p, starRingEnd ℂ (ψ (chi hζp a)) = ψ (chi hζp (-a)) := fun a =>
    conj_eq_of_mul_eq_one ψ (by rw [mul_comm]; exact chi_neg_mul hζp a) hp.out.ne_zero
      (chi_pow_eq_one hζp a)
  have hcq : ∀ b : ZMod N, starRingEnd ℂ (ψ (chiN hζq N b)) = ψ (chiN hζq N (-b)) := fun b =>
    conj_eq_of_mul_eq_one ψ (by rw [mul_comm]; exact chiN_neg_mul hζq hqN b) hq.out.ne_zero
      (chiN_pow_eq_one hζq N b)
  have hc : starRingEnd ℂ (ψ (hvalN hζp hζq u j t)) = ψ (hvalN' hζp hζq v j t) := by
    simp only [hvalN, hvalN', map_sum, map_mul, map_pow, hcu, hcp, hcq]
  have h := Complex.mul_conj (ψ (hvalN hζp hζq u j t))
  rw [hc, ← map_mul, hvalN_mul_hvalN' hζp hζq u v hqN hcorr, map_natCast,
    Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h.symm

variable [hK : IsCyclotomicExtension {p * q} ℚ K]

include hK in
/-- Lemma A along the rows: at a prime above `p`, for fixed `t`. -/
theorem psideN (hpq : p ≠ q) {e : ℕ} (hN : N = q ^ e)
    (hqN : q ∣ N) (hcorr : ∀ τ, ∑ g, u g * v (g + τ) = if τ = 0 then ((p * N : ℕ) : 𝓞 K) else 0)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] (t : ℕ) :
    ∃ (α : ℕ) (g : ℕ → Localization.AtPrime P), ∀ j < p,
      IsUnit (g j) ∧
      algebraMap (𝓞 K) (Localization.AtPrime P) (hvalN hζp hζq u j t) =
        algebraMap (𝓞 K) (Localization.AtPrime P) (hζp.toInteger - 1) ^ α * g j ∧
      g j - g 0 ∈ maximalIdeal (Localization.AtPrime P) := by
  have hpq' : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp.out hq.out).1 h)
  have he : P.ramificationIdx ℤ = p - 1 := by
    have := IsCyclotomicExtension.Rat.ramificationIdx_eq (p * q) K P
      (show p * q = p ^ (0 + 1) * q by ring) hpq'
    rwa [pow_zero, one_mul] at this
  have hy := IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hζp
  have hqP' : ((q : ℕ) : 𝓞 K) ∉ P := not_mem_of_liesOver hp.out hq.out hpq
  have hqP : ((N : ℕ) : 𝓞 K) ∉ P := by
    rw [hN, Nat.cast_pow]
    exact fun h => hqP' ((inferInstance : P.IsPrime).mem_of_pow_mem _ h)
  have e1 : ∀ j, ∑ g ∈ univ, (u g * chiN hζq N g.2 ^ t) * chi hζp g.1 ^ j = hvalN hζp hζq u j t :=
    fun j => by rw [hvalN]; exact Finset.sum_congr rfl fun g _ => by ring
  have e2 : ∀ j, ∑ g ∈ univ, (v g * chiN hζq N (-g.2) ^ t) * chi hζp (-g.1) ^ j =
      hvalN' hζp hζq v j t :=
    fun j => by rw [hvalN']; exact Finset.sum_congr rfl fun g _ => by ring
  obtain ⟨α, g, hg⟩ := lemmaA_localized p P he _ hy univ univ
    (fun g => u g * chiN hζq N g.2 ^ t) (fun g => chi hζp g.1)
    (fun g => v g * chiN hζq N (-g.2) ^ t) (fun g => chi hζp (-g.1))
    (fun g _ => sub_one_dvd_chi hζp g.1) (fun g _ => sub_one_dvd_chi hζp (-g.1)) _ hqP
    (fun j _ => by
      rw [e1, e2, hvalN_mul_hvalN' hζp hζq u v hqN hcorr, Nat.cast_mul])
  refine ⟨α, g, fun j hj => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hg j hj
  refine ⟨h1, ?_, h3⟩
  rw [← e1]
  exact h2

include hK in
/-- The ratio `W = h(0,0) h(j,t) / (h(j,0) h(0,t))` at a prime above `p`. -/
theorem ratio_pN (hpq : p ≠ q) {e : ℕ} (hN : N = q ^ e)
    (hqN : q ∣ N) (hcorr : ∀ τ, ∑ g, u g * v (g + τ) = if τ = 0 then ((p * N : ℕ) : 𝓞 K) else 0)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] {j t : ℕ}
    (hj : j < p) :
    ∃ a s : 𝓞 K, s ∉ P ∧
      hvalN hζp hζq u j 0 * hvalN hζp hζq u 0 t * a = hvalN hζp hζq u 0 0 * hvalN hζp hζq u j t * s ∧
      a - s ∈ P := by
  obtain ⟨α₀, g₀, hg₀⟩ := psideN hζp hζq u v hpq hN hqN hcorr P 0
  obtain ⟨αₜ, gₜ, hgₜ⟩ := psideN hζp hζq u v hpq hN hqN hcorr P t
  have hp0 := hp.out.pos
  refine exists_ratio_rep P _ _ _ _ _ α₀ αₜ (g₀ 0) (g₀ j) (gₜ j) (gₜ 0) (hg₀ j hj).1
    (hgₜ 0 hp0).1 (hg₀ 0 hp0).2.1 (hg₀ j hj).2.1 (hgₜ j hj).2.1 (hgₜ 0 hp0).2.1 ?_ (hgₜ j hj).2.2
  rw [← neg_sub]
  exact (Ideal.neg_mem_iff _).2 (hg₀ j hj).2.2

omit hK in
theorem hvalN_ne_zero
    (hqN : q ∣ N) (hcorr : ∀ τ, ∑ g, u g * v (g + τ) = if τ = 0 then ((p * N : ℕ) : 𝓞 K) else 0)
    (j t : ℕ) : hvalN hζp hζq u j t ≠ 0 := by
  intro h
  have := hvalN_mul_hvalN' hζp hζq u v hqN hcorr j t
  rw [h, zero_mul] at this
  exact (Nat.cast_ne_zero.2 (Nat.mul_ne_zero hp.out.ne_zero (NeZero.ne N))) this.symm

omit [NumberField K] in
/-- Orthogonality along the rows: `∑_j h(j, t) = p ρ(t)`, `ρ(t) = ∑_b u(0,b) ζ_q^{t b}`. -/
theorem sum_hvalN (t : ℕ) :
    ∑ j ∈ range p, hvalN hζp hζq u j t =
      (p : 𝓞 K) * ∑ b, u (0, b) * chiN hζq N b ^ t := by
  unfold hvalN
  rw [Finset.sum_comm]
  have : ∀ g : ZMod p × ZMod N, ∑ j ∈ range p, u g * chi hζp g.1 ^ j * chiN hζq N g.2 ^ t =
      u g * chiN hζq N g.2 ^ t * (if g.1 = 0 then (p : 𝓞 K) else 0) := fun g => by
    rw [← sum_chi_pow hζp g.1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [this]
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single 0 fun a ha => by simp [ha], Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by simp; ring

omit [NumberField K] in
theorem sum_hvalN' (t : ℕ) :
    ∑ j ∈ range p, hvalN' hζp hζq v j t =
      (p : 𝓞 K) * ∑ b, v (0, b) * chiN hζq N (-b) ^ t := by
  unfold hvalN'
  rw [Finset.sum_comm]
  have : ∀ g : ZMod p × ZMod N, ∑ j ∈ range p, v g * chi hζp (-g.1) ^ j * chiN hζq N (-g.2) ^ t =
      v g * chiN hζq N (-g.2) ^ t * (if g.1 = 0 then (p : 𝓞 K) else 0) := fun g => by
    have e : (if g.1 = 0 then (p : 𝓞 K) else 0) = if -g.1 = 0 then (p : 𝓞 K) else 0 := by
      simp [neg_eq_zero]
    rw [e, ← sum_chi_pow hζp (-g.1), Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [this]
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single 0 fun a ha => by simp [ha], Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by simp; ring

omit [NumberField K] in
/-- `ρ(t) ρ'(t) = ∑_s ζ_q^{-t s} A(s)` with `A(s) = ∑_b u(0,b) v(0,b+s)`. -/
theorem rho_mul_rhoN' (hqN : q ∣ N) (t : ℕ) :
    (∑ b, u (0, b) * chiN hζq N b ^ t) * (∑ b, v (0, b) * chiN hζq N (-b) ^ t) =
      ∑ s, chiN hζq N (-s) ^ t * ∑ b, u (0, b) * v (0, b + s) := by
  rw [Finset.sum_mul_sum]
  calc ∑ b, ∑ b', u (0, b) * chiN hζq N b ^ t * (v (0, b') * chiN hζq N (-b') ^ t)
      = ∑ b, ∑ s, u (0, b) * v (0, b + s) * chiN hζq N (-s) ^ t := by
        refine Finset.sum_congr rfl fun b _ => ?_
        refine (Fintype.sum_equiv (Equiv.addLeft b) _ _ fun s => ?_).symm
        simp only [Equiv.coe_addLeft]
        have h1 : chiN hζq N b * chiN hζq N (-(b + s)) = chiN hζq N (-s) := by
          rw [← chiN_add hζq hqN]; congr 1; ring
        rw [← h1]; ring
    _ = ∑ s, chiN hζq N (-s) ^ t * ∑ b, u (0, b) * v (0, b + s) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring


omit [NumberField K] in
/-- The convolution of the partial evaluations at a character of `C_p`. -/
theorem conv_partial (hcorr : ∀ τ, ∑ g, u g * v (g + τ) = if τ = 0 then ((p * N : ℕ) : 𝓞 K) else 0)
    (j : ℕ) (τ : ZMod N) :
    ∑ b, (∑ a, u (a, b) * chi hζp a ^ j) * (∑ a, v (a, -(τ - b)) * chi hζp (-a) ^ j) =
      if τ = 0 then ((p * N : ℕ) : 𝓞 K) else 0 := by
  calc ∑ b, (∑ a, u (a, b) * chi hζp a ^ j) * (∑ a, v (a, -(τ - b)) * chi hζp (-a) ^ j)
      = ∑ b, ∑ a, ∑ σ, u (a, b) * v ((a, b) + (σ, -τ)) * chi hζp (-σ) ^ j := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        refine (Fintype.sum_equiv (Equiv.addLeft a) _ _ fun σ => ?_).symm
        simp only [Equiv.coe_addLeft, Prod.mk_add_mk]
        have h1 : chi hζp a * chi hζp (-(a + σ)) = chi hζp (-σ) := by
          rw [← chi_add]; congr 1; ring
        have h2 : b + -τ = -(τ - b) := by ring
        rw [← h1, h2]; ring
    _ = ∑ σ, chi hζp (-σ) ^ j * ∑ g, u g * v (g + (σ, -τ)) := by
        simp_rw [Fintype.sum_prod_type, Finset.mul_sum]
        conv_lhs => rw [Finset.sum_comm]
        conv_lhs => enter [2, a]; rw [Finset.sum_comm]
        conv_lhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring
    _ = if τ = 0 then ((p * N : ℕ) : 𝓞 K) else 0 := by
        simp_rw [hcorr]
        rw [Fintype.sum_eq_single 0 fun σ hσ => by simp [hσ]]
        by_cases hτ : τ = 0 <;> simp [hτ, chi_zero]

omit hK in
/-- **The ratio at primes above `q`** via the unramified local comparison of the
circulant Hadamard formalization, applied to the partial evaluations in `ℤ[ζ_p][C_N]`. -/
theorem ratio_qN (hpq : p ≠ q) {e : ℕ} (hN : N = q ^ (e + 1)) (hqN : q ∣ N)
    (hcorr : ∀ τ, ∑ g, u g * v (g + τ) = if τ = 0 then ((p * N : ℕ) : 𝓞 K) else 0)
    (k : ZMod p × ZMod N → ℕ) (hu : ∀ g, u g = hζp.toInteger ^ k g)
    (hv : ∀ g, v g = hζp.toInteger ^ ((p - 1) * k g))
    (Q : Ideal (𝓞 K)) [hQ : Q.IsMaximal] (hqQ : ((q : ℕ) : 𝓞 K) ∈ Q) {j t : ℕ} (ht : t < q) :
    ∃ a s : 𝓞 K, s ∉ Q ∧
      hvalN hζp hζq u j 0 * hvalN hζp hζq u 0 t * a =
        hvalN hζp hζq u 0 0 * hvalN hζp hζq u j t * s ∧
      a - s ∈ Q := by
  classical
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · exact ⟨1, 1, fun h => hQ.ne_top ((Ideal.eq_top_iff_one _).2 h), by ring, by simp⟩
  -- a complex embedding and the coefficient order `ℤ[ζ_p] ⊂ ℂ`
  let φ₀ : K →+* ℂ := (IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom
  let Φ : 𝓞 K →+* ℂ := φ₀.comp (algebraMap (𝓞 K) K)
  have hΦ : Function.Injective Φ := φ₀.injective.comp RingOfIntegers.coe_injective
  set zp := hζp.toInteger with hzp
  set eta := Φ zp
  have hη : IsPrimitiveRoot eta p := hζp.toInteger_isPrimitiveRoot.map_of_injective hΦ
  obtain ⟨κ, hκ, hκgen⟩ := exists_order_hom Φ hΦ zp
  set gen := CyclotomicLocalBase.generator eta
  -- the contracted prime
  set m' : Ideal (CyclotomicLocalBase.Order eta) := Q.comap κ
  have : m'.IsPrime := Ideal.comap_isPrime κ Q
  have hint : Algebra.IsIntegral ℤ (CyclotomicLocalBase.Order eta) := by
    have := CyclotomicLocalBase.order_finite hη hp.out.pos
    infer_instance
  have hm'max : m'.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ℤ)
    have hcomp : m'.under ℤ = Q.under ℤ := by
      change m'.comap (algebraMap ℤ _) = Q.comap (algebraMap ℤ _)
      rw [Ideal.comap_comap]
      congr 1
      exact RingHom.ext_int _ _
    rw [hcomp]
    exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ) Q
  have hqm' : ((q : ℕ) : CyclotomicLocalBase.Order eta) ∈ m' := by
    show κ (q : CyclotomicLocalBase.Order eta) ∈ Q
    rw [map_natCast]; exact hqQ
  have hqp : ¬ q ∣ p := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).1 h).symm
  have hDVR := CyclotomicLocalBase.isDiscreteValuationRing hη hq.out hqp m' hqm'
  have hmax := CyclotomicLocalBase.maximalIdeal_eq_span hη hq.out hqp m' hqm'
  -- the root of order `q`
  set rho : 𝓞 K := hζq.toInteger ^ t with hrho_def
  have hcop : Nat.Coprime t q :=
    ((Nat.Prime.coprime_iff_not_dvd hq.out).2 (Nat.not_dvd_of_pos_of_lt ht0 ht)).symm
  have hprim : IsPrimitiveRoot rho q := hζq.toInteger_isPrimitiveRoot.pow_of_coprime t hcop
  have hrho : rho ^ q = 1 := hprim.pow_eq_one
  have hroot : (Polynomial.cyclotomic q (𝓞 K)).eval rho = 0 :=
    (Polynomial.isRoot_cyclotomic_iff.2 hprim)
  have hrhon : rho ^ N = 1 := by
    obtain ⟨c, hc⟩ := hqN; rw [hc, pow_mul, hrho, one_pow]
  have hc : IsUnit ((p : ℕ) : AlternatingLocalization.AtComap κ ⟨Q, hQ⟩) :=
    AlternatingLocalization.coprime_natCast_isUnit m' q p (Nat.coprime_comm.1
      ((Nat.coprime_primes hp.out hq.out).2 hpq)) hqm'
  -- the partial evaluations, as elements of `ℤ[ζ_p][C_N]`
  let Fj : ℕ → CyclicRing.Elem (CyclotomicLocalBase.Order eta) N := fun j' =>
    CyclicRing.ofCoeffs (fun b => ∑ a : ZMod p, gen ^ k (a, b) * gen ^ (j' * a.val))
  let Kj : ℕ → CyclicRing.Elem (CyclotomicLocalBase.Order eta) N := fun j' =>
    CyclicRing.ofCoeffs (fun b => ∑ a : ZMod p,
      gen ^ ((p - 1) * k (a, -b)) * gen ^ (j' * (-a).val))
  have hκF : ∀ j' b, κ ((Fj j').coeff b) = ∑ a, u (a, b) * chi hζp a ^ j' := by
    intro j' b
    simp only [Fj, CyclicRing.ofCoeffs_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, map_pow, map_pow, hκgen, hu, chi, ← pow_mul, mul_comm a.val j']
  have hκK : ∀ j' b, κ ((Kj j').coeff b) = ∑ a, v (a, -b) * chi hζp (-a) ^ j' := by
    intro j' b
    simp only [Kj, CyclicRing.ofCoeffs_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, map_pow, map_pow, hκgen, hv, chi, ← pow_mul, mul_comm (-a).val j']
  have hFK : ∀ j', Fj j' * Kj j' = CyclicRing.scalar N
      (((q : ℕ) : CyclotomicLocalBase.Order eta) ^ (e + 1) *
        ((p : ℕ) : CyclotomicLocalBase.Order eta)) := by
    intro j'
    ext τ : 2
    apply hκ
    rw [CyclicRing.mul_apply, CyclicRing.scalar_apply, map_sum]
    simp_rw [map_mul, hκF, hκK]
    rw [conv_partial hζp u v hcorr j' τ]
    split_ifs <;> simp [hN, mul_comm]
  -- evaluations
  have hev : ∀ j', CyclicRing.evaluate κ
      (CyclicPolynomial.powerCharacter N rho hrhon) (Fj j') = hvalN hζp hζq u j' t := by
    intro j'
    rw [CyclicRing.evaluate_apply]
    simp_rw [hκF, CyclicPolynomial.powerCharacter_apply]
    unfold hvalN
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [chiN, hrho_def, ← pow_mul]
    ring
  have hev0 : ∀ j', CyclicRing.evaluate κ 1 (Fj j') = hvalN hζp hζq u j' 0 := by
    intro j'
    rw [CyclicRing.evaluate_apply]
    simp_rw [hκF, MonoidHom.one_apply, mul_one]
    unfold hvalN
    simp only [pow_zero, mul_one]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hassoc := fun j' => AlternatingLocalization.actual_local_character_association κ ⟨Q, hQ⟩
    q hq.out hqQ hmax rho hrho hroot N e p hN hrhon hc (Fj j') (Kj j') (hFK j')
  obtain ⟨Uj, hUj, hresj⟩ := hassoc j
  obtain ⟨U0, hU0, hres0⟩ := hassoc 0
  rw [hev, hev0] at hUj hU0
  set L := Localization.AtPrime Q
  set φ := algebraMap (𝓞 K) L
  refine exists_rep_of_unit Q _ _ ((Uj : L) * ↑U0⁻¹) ?_ ?_
  · change φ (hvalN hζp hζq u j 0 * hvalN hζp hζq u 0 t) * ((Uj : L) * ↑U0⁻¹) =
      φ (hvalN hζp hζq u 0 0 * hvalN hζp hζq u j t)
    rw [map_mul, map_mul, hUj, hU0]
    calc φ (hvalN hζp hζq u j 0) * (↑U0 * φ (hvalN hζp hζq u 0 0)) * (↑Uj * ↑U0⁻¹)
        = φ (hvalN hζp hζq u 0 0) * (↑Uj * φ (hvalN hζp hζq u j 0)) * (↑U0 * ↑U0⁻¹) := by ring
      _ = _ := by rw [Units.mul_inv, mul_one]
  · rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_mul, hresj,
      LocalComparison.residue_inv_eq_one _ hres0, map_one, mul_one, sub_self]

include hK in
/-- **The key step `W = 1`**: `h(0,0) h(j,t) = h(j,0) h(0,t)`. -/
theorem hvalN_rel (hpq : p ≠ q) {e : ℕ} (hN : N = q ^ (e + 1)) (hqN : q ∣ N)
    (hcorr : ∀ τ, ∑ g, u g * v (g + τ) = if τ = 0 then ((p * N : ℕ) : 𝓞 K) else 0)
    (k : ZMod p × ZMod N → ℕ) (hu : ∀ g, u g = hζp.toInteger ^ k g)
    (hv : ∀ g, v g = hζp.toInteger ^ ((p - 1) * k g)) (huv : ∀ g, u g * v g = 1)
    {j t : ℕ} (hj : j < p) (ht : t < q) :
    hvalN hζp hζq u 0 0 * hvalN hζp hζq u j t = hvalN hζp hζq u j 0 * hvalN hζp hζq u 0 t := by
  classical
  set A := hvalN hζp hζq u 0 0 * hvalN hζp hζq u j t with hA
  set B := hvalN hζp hζq u j 0 * hvalN hζp hζq u 0 t with hB
  set ι := algebraMap (𝓞 K) K
  have hι : Function.Injective ι := RingOfIntegers.coe_injective
  have hB0 : B ≠ 0 := mul_ne_zero (hvalN_ne_zero hζp hζq u v hqN hcorr _ _)
    (hvalN_ne_zero hζp hζq u v hqN hcorr _ _)
  have hA0 : A ≠ 0 := mul_ne_zero (hvalN_ne_zero hζp hζq u v hqN hcorr _ _)
    (hvalN_ne_zero hζp hζq u v hqN hcorr _ _)
  have hιB : ι B ≠ 0 := (map_ne_zero_iff _ hι).2 hB0
  set W : K := ι A / ι B with hW
  -- `W = a / s` from `B a = A s`
  have hdiv : ∀ a s : 𝓞 K, s ≠ 0 → B * a = A * s → W = ι a / ι s := by
    intro a s hs h
    have hιs : ι s ≠ 0 := (map_ne_zero_iff _ hι).2 hs
    rw [hW, div_eq_div_iff hιB hιs, ← map_mul, ← map_mul, mul_comm a B, h]
  have hpq' : (((p * N : ℕ) : 𝓞 K)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Nat.cast_ne_zero.2 (Nat.mul_ne_zero hp.out.ne_zero (NeZero.ne N)))
  -- integrality of `W`
  obtain ⟨w, hw⟩ : ∃ w : 𝓞 K, ι w = W := by
    refine mem_range_of_forall_maximal W fun 𝔓 h𝔓 => ?_
    by_cases hpP : ((p : ℕ) : 𝓞 K) ∈ 𝔓
    · have := liesOver_of_mem hp.out hpP
      obtain ⟨a, s, hs, hrel, -⟩ := ratio_pN hζp hζq u v hpq hN hqN hcorr 𝔓 hj (t := t)
      exact ⟨a, s, hs, hdiv a s (fun h => hs (h ▸ 𝔓.zero_mem)) hrel⟩
    by_cases hqP : ((q : ℕ) : 𝓞 K) ∈ 𝔓
    · have := h𝔓
      obtain ⟨a, s, hs, hrel, -⟩ := ratio_qN hζp hζq u v hpq hN hqN hcorr k hu hv 𝔓 hqP ht (j := j)
      exact ⟨a, s, hs, hdiv a s (fun h => hs (h ▸ 𝔓.zero_mem)) hrel⟩
    · refine ⟨A * (hvalN' hζp hζq v j 0 * hvalN' hζp hζq v 0 t), ((p * N : ℕ) : 𝓞 K) ^ 2,
        fun h => ?_, hdiv _ _ hpq' ?_⟩
      · have h' := h𝔓.isPrime.mem_of_pow_mem 2 h
        rw [Nat.cast_mul] at h'
        rcases h𝔓.isPrime.mem_or_mem h' with h'' | h''
        · exact hpP h''
        · rw [hN, Nat.cast_pow] at h''
          exact hqP (h𝔓.isPrime.mem_of_pow_mem _ h'')
      · rw [hB, pow_two]
        have e1 := hvalN_mul_hvalN' hζp hζq u v hqN hcorr j 0
        have e2 := hvalN_mul_hvalN' hζp hζq u v hqN hcorr 0 t
        calc hvalN hζp hζq u j 0 * hvalN hζp hζq u 0 t *
              (A * (hvalN' hζp hζq v j 0 * hvalN' hζp hζq v 0 t))
            = A * ((hvalN hζp hζq u j 0 * hvalN' hζp hζq v j 0) *
                (hvalN hζp hζq u 0 t * hvalN' hζp hζq v 0 t)) := by ring
          _ = _ := by rw [e1, e2]
  -- `|σ W| = 1` for every embedding
  have hnorm : ∀ φ : K →+* ℂ, ‖φ W‖ = 1 := by
    intro φ
    set ψ := φ.comp ι
    have hn := fun j t => norm_sq_hvalN hζp hζq u v hqN hcorr (fun g => ⟨k g, hu g⟩) huv ψ j t
    have hpos : (0 : ℝ) < p * N := by
      have := hp.out.pos; have : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N); positivity
    have heq : ∀ j t j' t', ‖ψ (hvalN hζp hζq u j t)‖ = ‖ψ (hvalN hζp hζq u j' t')‖ :=
      fun j t j' t' => (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
        ((hn j t).trans (hn j' t').symm)
    have hne : ‖ψ (hvalN hζp hζq u 0 0)‖ ≠ 0 := by
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
  have hqQ : ((q : ℕ) : 𝓞 K) ∈ Q := by
    have : (q : ℤ) ∈ Q.under ℤ := by
      rw [← Ideal.over_def Q (Ideal.span {(q : ℤ)})]
      exact Ideal.subset_span rfl
    simpa using this
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
    obtain ⟨a, s, hs, hrel, hmem⟩ := ratio_pN hζp hζq u v hpq hN hqN hcorr P hj (t := t)
    exact hsub P a s hs hrel hmem
  have hwQ : w - 1 ∈ Q := by
    obtain ⟨a, s, hs, hrel, hmem⟩ := ratio_qN hζp hζq u v hpq hN hqN hcorr k hu hv Q hqQ ht (j := j)
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

include hK hζq in
/-- **Theorem C for `m = q ^ e`, ring-theoretic form.** -/
theorem theoremC_coreN (hpq : p ≠ q) {e : ℕ} (hN : N = q ^ (e + 1)) (hqN : q ∣ N)
    (hcorr : ∀ τ, ∑ g, u g * v (g + τ) = if τ = 0 then ((p * N : ℕ) : 𝓞 K) else 0)
    (k : ZMod p × ZMod N → ℕ) (hu : ∀ g, u g = hζp.toInteger ^ k g)
    (hv : ∀ g, v g = hζp.toInteger ^ ((p - 1) * k g)) (huv : ∀ g, u g * v g = 1) : False := by
  classical
  set M : 𝓞 K := ((p * N : ℕ) : 𝓞 K) with hM
  have hM0 : M ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_ne_zero hp.out.ne_zero (NeZero.ne N))
  have hp0 : (p : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hq0 : (q : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hq.out.ne_zero
  have hhh := hvalN_mul_hvalN' hζp hζq u v hqN hcorr
  have hrel := fun {j t : ℕ} (hj : j < p) (ht : t < q) =>
    hvalN_rel hζp hζq u v hpq hN hqN hcorr k hu hv huv hj ht
  -- the same relation for `h'`
  have hrel' : ∀ {j t : ℕ}, j < p → t < q →
      hvalN' hζp hζq v 0 0 * hvalN' hζp hζq v j t = hvalN' hζp hζq v j 0 * hvalN' hζp hζq v 0 t := by
    intro j t hj ht
    have hX : hvalN hζp hζq u 0 0 * hvalN hζp hζq u j t ≠ 0 :=
      mul_ne_zero (hvalN_ne_zero hζp hζq u v hqN hcorr _ _) (hvalN_ne_zero hζp hζq u v hqN hcorr _ _)
    apply mul_left_cancel₀ hX
    calc hvalN hζp hζq u 0 0 * hvalN hζp hζq u j t *
          (hvalN' hζp hζq v 0 0 * hvalN' hζp hζq v j t)
        = (hvalN hζp hζq u 0 0 * hvalN' hζp hζq v 0 0) *
            (hvalN hζp hζq u j t * hvalN' hζp hζq v j t) := by ring
      _ = (hvalN hζp hζq u j 0 * hvalN' hζp hζq v j 0) *
            (hvalN hζp hζq u 0 t * hvalN' hζp hζq v 0 t) := by rw [hhh, hhh, hhh, hhh]
      _ = hvalN hζp hζq u 0 0 * hvalN hζp hζq u j t *
            (hvalN' hζp hζq v j 0 * hvalN' hζp hζq v 0 t) := by rw [hrel hj ht]; ring
  set ρ : ℕ → 𝓞 K := fun t => ∑ b, u (0, b) * chiN hζq N b ^ t with hρ
  set ρ' : ℕ → 𝓞 K := fun t => ∑ b, v (0, b) * chiN hζq N (-b) ^ t with hρ'
  -- summing the relations over `j`
  have hsum : ∀ t < q, hvalN hζp hζq u 0 0 * ((p : 𝓞 K) * ρ t) =
      hvalN hζp hζq u 0 t * ((p : 𝓞 K) * ρ 0) := by
    intro t ht
    rw [hρ]; dsimp only
    rw [← sum_hvalN hζp hζq u t, ← sum_hvalN hζp hζq u 0, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj => by
      rw [hrel (Finset.mem_range.1 hj) ht]; ring
  have hsum' : ∀ t < q, hvalN' hζp hζq v 0 0 * ((p : 𝓞 K) * ρ' t) =
      hvalN' hζp hζq v 0 t * ((p : 𝓞 K) * ρ' 0) := by
    intro t ht
    rw [hρ']; dsimp only
    rw [← sum_hvalN' hζp hζq v t, ← sum_hvalN' hζp hζq v 0, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj => by
      rw [hrel' (Finset.mem_range.1 hj) ht]; ring
  have hconst : ∀ t < q, ρ t * ρ' t = ρ 0 * ρ' 0 := by
    intro t ht
    have h := congrArg₂ (· * ·) (hsum t ht) (hsum' t ht)
    have hpN : (p : 𝓞 K) * (p : 𝓞 K) * M ≠ 0 := mul_ne_zero (mul_ne_zero hp0 hp0) hM0
    apply mul_left_cancel₀ hpN
    calc (p : 𝓞 K) * p * M * (ρ t * ρ' t)
        = hvalN hζp hζq u 0 0 * hvalN' hζp hζq v 0 0 * (p * p) * (ρ t * ρ' t) := by
          rw [hhh, ← hM]; ring
      _ = hvalN hζp hζq u 0 0 * (p * ρ t) * (hvalN' hζp hζq v 0 0 * (p * ρ' t)) := by ring
      _ = hvalN hζp hζq u 0 t * (p * ρ 0) * (hvalN' hζp hζq v 0 t * (p * ρ' 0)) := h
      _ = hvalN hζp hζq u 0 t * hvalN' hζp hζq v 0 t * (p * p) * (ρ 0 * ρ' 0) := by ring
      _ = (p : 𝓞 K) * p * M * (ρ 0 * ρ' 0) := by rw [hhh, ← hM]; ring
  -- Fourier inversion over the characters of order `q`, at the shift `1`
  set A : ZMod N → 𝓞 K := fun s => ∑ b, u (0, b) * v (0, b + s) with hA
  set S : Finset (ZMod N) := Finset.univ.filter (fun s : ZMod N => q ∣ (1 - s).val) with hS
  have hN1 : 1 < N := by
    rw [hN]; exact Nat.one_lt_pow (Nat.succ_ne_zero e) hq.out.one_lt
  have : Fact (1 < N) := ⟨hN1⟩
  have hq1 : ¬ q ∣ (1 : ZMod N).val := by
    rw [ZMod.val_one]; exact hq.out.not_dvd_one
  have hchi1 : ∀ s : ZMod N, chiN hζq N 1 * chiN hζq N (-s) = chiN hζq N (1 - s) := fun s => by
    rw [← chiN_add hζq hqN, sub_eq_add_neg]
  -- the row sum `∑_{s ∈ S} A(s)` vanishes
  have hF : ∑ t ∈ range q, chiN hζq N 1 ^ t * (ρ t * ρ' t) = (q : 𝓞 K) * ∑ s ∈ S, A s := by
    calc ∑ t ∈ range q, chiN hζq N 1 ^ t * (ρ t * ρ' t)
        = ∑ t ∈ range q, ∑ s, A s * chiN hζq N (1 - s) ^ t := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hρ, hρ']; dsimp only
          rw [rho_mul_rhoN' hζq u v hqN, Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [← hchi1 s, mul_pow]; ring
      _ = ∑ s, A s * ∑ t ∈ range q, chiN hζq N (1 - s) ^ t := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun s _ => by rw [Finset.mul_sum]
      _ = (q : 𝓞 K) * ∑ s ∈ S, A s := by
          simp_rw [sum_chiN_pow hζq N]
          rw [hS, Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          split_ifs <;> ring
  have hF' : ∑ t ∈ range q, chiN hζq N 1 ^ t * (ρ t * ρ' t) = 0 := by
    rw [Finset.sum_congr rfl fun t ht => by rw [hconst t (Finset.mem_range.1 ht)],
      ← Finset.sum_mul, sum_chiN_pow hζq N]
    simp [hq1]
  have hSA : ∑ s ∈ S, A s = 0 := by
    have := hF.symm.trans hF'
    exact (mul_eq_zero.1 this).resolve_left hq0
  -- `q · |S| = N`
  have hcard : (q : 𝓞 K) * (S.card : 𝓞 K) = (N : 𝓞 K) := by
    have h1 : ∑ t ∈ range q, ∑ s : ZMod N, chiN hζq N (1 - s) ^ t = (q : 𝓞 K) * S.card := by
      rw [Finset.sum_comm]
      simp_rw [sum_chiN_pow hζq N]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s : ZMod N => q ∣ (1 - s).val)]
      rw [Finset.sum_congr rfl fun s hs => ite_eq_left_iff.2 fun h =>
          absurd (Finset.mem_filter.1 hs).2 h,
        Finset.sum_congr rfl fun s hs => ite_eq_right_iff.2 fun h =>
          absurd h (Finset.mem_filter.1 hs).2]
      simp [hS, mul_comm]
    have h2 : ∑ t ∈ range q, ∑ s : ZMod N, chiN hζq N (1 - s) ^ t = (N : 𝓞 K) := by
      have : ∀ t, ∑ s : ZMod N, chiN hζq N (1 - s) ^ t = ∑ s : ZMod N, chiN hζq N s ^ t :=
        fun t => Fintype.sum_equiv (Equiv.subLeft 1) _ _ fun s => rfl
      simp_rw [this, sum_chiN_pow_univ hζq hqN]
      rw [Finset.sum_eq_single 0 (fun t ht ht0 => by
          exact ite_eq_right_iff.2 fun h =>
            absurd (Nat.eq_zero_of_dvd_of_lt h (Finset.mem_range.1 ht)) ht0)
        (fun h => absurd (Finset.mem_range.2 hq.out.pos) h)]
      simp
    rw [← h1, h2]
  -- but `∑_{s ∈ S} A(s) ≡ |S| N (mod ζ_p - 1)`
  have hdvd : hζp.toInteger - 1 ∣ ∑ s ∈ S, A s - (S.card : 𝓞 K) * N := by
    have hs : ∀ s, ∑ b : ZMod N, (u (0, b) * v (0, b + s) - 1) = A s - N := fun s => by
      rw [Finset.sum_sub_distrib, hA]
      simp [Finset.card_univ, ZMod.card]
    have : ∑ s ∈ S, A s - (S.card : 𝓞 K) * N =
        ∑ s ∈ S, ∑ b : ZMod N, (u (0, b) * v (0, b + s) - 1) := by
      rw [Finset.sum_congr rfl fun s _ => hs s, Finset.sum_sub_distrib, Finset.sum_const,
        nsmul_eq_mul]
    rw [this]
    refine Finset.dvd_sum fun s _ => Finset.dvd_sum fun b _ => ?_
    rw [hu, hv, ← pow_add]
    simpa [one_pow] using sub_dvd_pow_sub_pow hζp.toInteger 1 (k (0, b) + (p - 1) * k (0, b + s))
  rw [hSA, zero_sub, dvd_neg] at hdvd
  have hdvd2 : hζp.toInteger - 1 ∣ (N : 𝓞 K) ^ 2 := by
    have := hdvd.mul_left (q : 𝓞 K)
    rw [← mul_assoc, hcard] at this
    rw [pow_two]; exact this
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
    obtain ⟨c, hc⟩ := hdvd2
    have hN2 : (N : 𝓞 K) ^ 2 ∈ P := by rw [hc]; exact P.mul_mem_right _ hyP
    rw [hN, Nat.cast_pow, ← pow_mul] at hN2
    exact hPmax.isPrime.mem_of_pow_mem _ hN2
  exact not_mem_of_liesOver hp.out hq.out hpq hqP

end SetupN

end CirculantHadamard.RamifiedComparison

end OAI

namespace OAI

namespace CirculantHadamard.RamifiedComparison

open NumberField Finset

theorem not_exists_perfect_prime_power_phase_aux (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (e : ℕ) (K : Type*) [Field K] [NumberField K] [NeZero (p * q)]
    [IsCyclotomicExtension {p * q} ℚ K] :
    ¬ ∃ a : ZMod (p * q ^ (e + 1)) → ℂ,
      (∀ j, a j ^ p = 1) ∧
      ∀ τ : ZMod (p * q ^ (e + 1)), τ ≠ 0 →
        ∑ j, a j * (starRingEnd ℂ) (a (j + τ)) = 0 := by
  classical
  rintro ⟨a, ha, hauto⟩
  have hN : q ^ (e + 1) = q ^ (e + 1) := rfl
  have : NeZero (q ^ (e + 1)) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  have hqN : q ∣ q ^ (e + 1) := dvd_pow_self q (Nat.succ_ne_zero e)
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
  have hcop : p.Coprime (q ^ (e + 1)) := Nat.Coprime.pow_right _ ((Nat.coprime_primes hp.out hq.out).2 hpq)
  let ε : ZMod (p * q ^ (e + 1)) ≃+* ZMod p × ZMod (q ^ (e + 1)) := ZMod.chineseRemainder hcop
  have hk : ∀ x, ∃ i < p, Φ zp ^ i = a x := fun x => hω.eq_pow_of_pow_eq_one (ha x)
  choose k _ hk using hk
  let u : ZMod p × ZMod (q ^ (e + 1)) → 𝓞 K := fun g => zp ^ k (ε.symm g)
  let v : ZMod p × ZMod (q ^ (e + 1)) → 𝓞 K := fun g => zp ^ ((p - 1) * k (ε.symm g))
  have hzp : zp ^ p = 1 := hζp.toInteger_isPrimitiveRoot.pow_eq_one
  have huv : ∀ g, u g * v g = 1 := fun g => by
    simp only [u, v]
    rw [← pow_add, show k (ε.symm g) + (p - 1) * k (ε.symm g) = p * k (ε.symm g) by
      have := hp.out.one_le
      zify [this]; ring, pow_mul, hzp, one_pow]
  have hΦu : ∀ g, Φ (u g) = a (ε.symm g) := fun g => by
    simp only [u, map_pow]; exact hk _
  have hΦv : ∀ g, Φ (v g) = (starRingEnd ℂ) (a (ε.symm g)) := fun g => by
    rw [← hΦu, conj_eq_of_mul_eq_one Φ (huv g) hp.out.ne_zero (by
      simp only [u]; rw [← pow_mul, mul_comm (k _) p, pow_mul, hzp, one_pow])]
  have hcorr : ∀ τ, ∑ g, u g * v (g + τ) = if τ = 0 then ((p * q ^ (e + 1) : ℕ) : 𝓞 K) else 0 := by
    intro τ
    split_ifs with hτ
    · subst hτ
      simp only [add_zero, huv, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        ZMod.card, nsmul_eq_mul, mul_one, Nat.cast_mul]
    · apply hΦinj
      rw [map_sum, map_zero]
      simp only [map_mul, hΦu, hΦv, map_add ε.symm]
      have hτ' : ε.symm τ ≠ 0 := by
        intro h; apply hτ
        rw [← ε.apply_symm_apply τ, h, map_zero]
      rw [← hauto (ε.symm τ) hτ']
      exact Fintype.sum_equiv ε.symm.toEquiv _ _ fun g => rfl
  exact theoremC_coreN hζp hζq u v hpq hN hqN hcorr (fun g => k (ε.symm g)) (fun g => rfl)
    (fun g => rfl) huv

/-- **Theorem C (`m = q ^ e`, `e ≥ 1`).** For primes `p ≠ q` there is no perfect sequence
of length `p q ^ e` whose entries are `p`-th roots of unity: no `a : ZMod (p q ^ e) → ℂ`
with `a j ^ p = 1` has all nontrivial periodic autocorrelations equal to zero. -/
theorem not_exists_perfect_prime_power_phase (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (e : ℕ) (he : 1 ≤ e) :
    ¬ ∃ a : ZMod (p * q ^ e) → ℂ,
      (∀ j, a j ^ p = 1) ∧
      ∀ τ : ZMod (p * q ^ e), τ ≠ 0 →
        ∑ j, a j * (starRingEnd ℂ) (a (j + τ)) = 0 := by
  have : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.out.ne_zero hq.out.ne_zero⟩
  have hcyc : IsCyclotomicExtension {p * q} ℚ (CyclotomicField (p * q) ℚ) := by
    convert (inferInstance : @IsCyclotomicExtension {p * q} ℚ (CyclotomicField (p * q) ℚ) _ _
      (CyclotomicField.algebra (p * q) ℚ))
    exact Subsingleton.elim _ _
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  exact not_exists_perfect_prime_power_phase_aux p q hpq e' (CyclotomicField (p * q) ℚ)

end CirculantHadamard.RamifiedComparison

end OAI
