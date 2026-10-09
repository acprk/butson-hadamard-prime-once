import OAI.LinearAlgebra.CirculantHadamard.RamifiedComparison.Core

/-!
# Lemma A over `ℤ[ζ_p]` (the case `d = 1`)

Let `p` be a prime, `K = ℚ(ζ_p)`, and let `F, V ∈ 𝓞_K[C_p]` with `F * V = n`, where `n`
is a rational integer with `v_p(n) = 1`. Then, writing `F(ζ^j) = ∑ₐ F(a) ζ^{ja}` and
`λ = ζ - 1`, there is `α` such that for every `j`:

* `λ ^ α ∣ F(ζ^j)` and `λ ^ (α+1) ∤ F(ζ^j)` (the `λ`-adic valuation is independent of `j`);
* `λ ^ (α+1) ∣ F(ζ^j) - F(1)` (so `F(ζ^j) / F(1) ≡ 1 (mod λ)`).

The typical application is `V = F^*` (so `F F^* = n`), but no conjugation is needed.
-/

namespace OAI

namespace CirculantHadamard.RamifiedComparison

open NumberField Finset

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [hK : IsCyclotomicExtension {p} ℚ K] {ζ : K}

omit [NumberField K] hK in
/-- `ζ ^ x` only depends on `x mod p`. -/
theorem toInteger_pow_mod (hζ : IsPrimitiveRoot ζ p) (x : ℕ) :
    hζ.toInteger ^ x = hζ.toInteger ^ (x % p) := by
  conv_lhs => rw [← Nat.div_add_mod x p, pow_add, pow_mul, hζ.toInteger_isPrimitiveRoot.pow_eq_one,
    one_pow, one_mul]

omit [NumberField K] hK in
/-- The character `a ↦ ζ ^ a` of `ZMod p`. -/
theorem toInteger_pow_val_add (hζ : IsPrimitiveRoot ζ p) (a b : ZMod p) :
    hζ.toInteger ^ (a + b).val = hζ.toInteger ^ a.val * hζ.toInteger ^ b.val := by
  rw [← pow_add, toInteger_pow_mod hζ (a.val + b.val), ZMod.val_add]

omit [NumberField K] hK in
/-- Evaluation of a convolution product at a character. -/
theorem eval_mul_eval (hζ : IsPrimitiveRoot ζ p) (u v : ZMod p → 𝓞 K) (j : ℕ) :
    (∑ a, u a * (hζ.toInteger ^ a.val) ^ j) * (∑ b, v b * (hζ.toInteger ^ b.val) ^ j) =
      ∑ τ, (∑ a, u a * v (τ - a)) * (hζ.toInteger ^ τ.val) ^ j := by
  calc (∑ a, u a * (hζ.toInteger ^ a.val) ^ j) * (∑ b, v b * (hζ.toInteger ^ b.val) ^ j)
      = ∑ a, ∑ b, u a * v b * (hζ.toInteger ^ (a + b).val) ^ j := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [toInteger_pow_val_add hζ, mul_pow]; ring
    _ = ∑ a, ∑ τ, u a * v (τ - a) * (hζ.toInteger ^ τ.val) ^ j := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Fintype.sum_equiv (Equiv.addLeft a) _ _ fun b => by simp
    _ = ∑ τ, (∑ a, u a * v (τ - a)) * (hζ.toInteger ^ τ.val) ^ j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Finset.sum_mul]

/-- **Lemma A for `ℤ[ζ_p]`.** -/
theorem lemmaA_prime (hζ : IsPrimitiveRoot ζ p) (u v : ZMod p → 𝓞 K) (n : ℤ)
    (hn₁ : (p : ℤ) ∣ n) (hn₂ : ¬ (p : ℤ) ^ 2 ∣ n)
    (huv : ∀ τ : ZMod p, ∑ a, u a * v (τ - a) = if τ = 0 then (n : 𝓞 K) else 0) :
    ∃ α : ℕ, ∀ j : ℕ,
      (hζ.toInteger - 1) ^ α ∣ ∑ a, u a * hζ.toInteger ^ (j * a.val) ∧
      ¬ (hζ.toInteger - 1) ^ (α + 1) ∣ ∑ a, u a * hζ.toInteger ^ (j * a.val) ∧
      (hζ.toInteger - 1) ^ (α + 1) ∣ (∑ a, u a * hζ.toInteger ^ (j * a.val)) - ∑ a, u a := by
  set y : 𝓞 K := hζ.toInteger - 1 with hy_def
  have hprime : Prime y := hζ.zeta_sub_one_prime'
  have hy0 : y ≠ 0 := hprime.ne_zero
  have hmax : (Ideal.span {y}).IsMaximal := by
    refine Ideal.IsPrime.isMaximal ?_ ?_
    · exact (Ideal.span_singleton_prime hy0).2 hprime
    · rwa [Ne, Ideal.span_singleton_eq_bot]
  have hpy : y ∣ (p : 𝓞 K) := hζ.toInteger_sub_one_dvd_prime'
  -- `n = y ^ (p - 1) * ν` with `y ∤ ν`
  obtain ⟨m, rfl⟩ := hn₁
  have hm : ¬ (p : ℤ) ∣ m := fun h => hn₂ (by rw [pow_two]; exact mul_dvd_mul_left _ h)
  obtain ⟨w, hw⟩ := IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hζ
  have hν : ¬ y ∣ (w : 𝓞 K) * (m : 𝓞 K) := by
    intro h
    rcases hprime.dvd_or_dvd h with h | h
    · exact hprime.not_isUnit (isUnit_of_dvd_unit h w.isUnit)
    · exact hm ((IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff' p hζ).1 h)
  have hprod : ∀ j < p,
      (∑ a, u a * (hζ.toInteger ^ a.val) ^ j) * (∑ b, v b * (hζ.toInteger ^ b.val) ^ j) =
        y ^ (p - 1) * ((w : 𝓞 K) * (m : 𝓞 K)) := by
    intro j _
    rw [eval_mul_eval hζ, Fintype.sum_eq_single 0 (fun τ hτ => by simp [huv τ, hτ])]
    simp only [huv 0, ↓reduceIte]
    rw [ZMod.val_zero, pow_zero, one_pow, mul_one, ← mul_assoc, hw]
    push_cast; ring
  obtain ⟨α, hα⟩ := ramified_comparison_core p hp.out y hy0 hmax hpy Finset.univ Finset.univ
    u (fun a => hζ.toInteger ^ a.val) v (fun b => hζ.toInteger ^ b.val)
    (fun a _ => by simpa [one_pow] using sub_dvd_pow_sub_pow hζ.toInteger 1 a.val)
    (fun b _ => by simpa [one_pow] using sub_dvd_pow_sub_pow hζ.toInteger 1 b.val)
    _ hν hprod
  refine ⟨α, fun j => ?_⟩
  have hred : ∀ a : ZMod p, hζ.toInteger ^ (j * a.val) = (hζ.toInteger ^ a.val) ^ (j % p) := by
    intro a
    rw [← pow_mul, toInteger_pow_mod hζ (j * a.val), toInteger_pow_mod hζ (a.val * (j % p))]
    congr 1
    conv_rhs => rw [mul_comm, Nat.mod_mul_mod]
  simp_rw [hred]
  have h0 : ∑ a, u a = ∑ a, u a * (hζ.toInteger ^ a.val) ^ 0 := by simp
  rw [h0]
  exact hα (j % p) (Nat.mod_lt _ hp.out.pos)

end CirculantHadamard.RamifiedComparison

end OAI
