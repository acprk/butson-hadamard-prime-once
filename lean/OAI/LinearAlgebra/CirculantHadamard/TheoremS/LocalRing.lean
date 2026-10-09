import Mathlib

/-!
# Theorem S, local step: `F[C_p]` is local in characteristic `p`

Let `F` be a field of characteristic `p` and let `x w : ZMod p → F`.  View them as the
group-ring elements `X = ∑ x(y) T^y` and `W = ∑ w(y) T^{-y}` of `F[C_p]`.  The
coefficients of `X * W` are the correlations `∑_y x(y+s) w(y)`.  If `X * W = 0` and the
augmentation `∑_y x(y)` of `X` is nonzero, then `W = 0`.

The proof goes through `F[T]`: `X * W ≡ 0 (mod T^p - 1)` and `T^p - 1 = (T - 1)^p` in
characteristic `p`; `T - 1` does not divide `X` (because `X(1) ≠ 0`), so `(T-1)^p ∣ W`, which
forces `W = 0` by degree.
-/

namespace OAI.CirculantHadamard.TheoremS

open Polynomial Finset

variable {F : Type*} [Field F] {p : ℕ} [hp : Fact p.Prime]

omit hp in
/-- `T^p - 1` divides `T^a - T^(a % p)`. -/
lemma X_pow_sub_X_pow_mod_dvd (a : ℕ) :
    (X ^ p - 1 : F[X]) ∣ X ^ a - X ^ (a % p) := by
  have h : (X : F[X]) ^ a - X ^ (a % p) = X ^ (a % p) * ((X ^ p) ^ (a / p) - 1 ^ (a / p)) := by
    rw [one_pow, mul_sub, mul_one, ← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [h]
  exact Dvd.dvd.mul_left (sub_dvd_pow_sub_pow _ _ _) _

/-- **Local step.**  In characteristic `p`, if all correlations of `x` against `w` vanish and
`∑ x ≠ 0`, then `w = 0`. -/
theorem eq_zero_of_corr_eq_zero [CharP F p] (x w : ZMod p → F)
    (hcorr : ∀ s : ZMod p, ∑ y, x (y + s) * w y = 0) (hx : ∑ y, x y ≠ 0) (y : ZMod p) :
    w y = 0 := by
  classical
  set fx : F[X] := ∑ y : ZMod p, C (x y) * X ^ y.val with hfx
  set fw : F[X] := ∑ y : ZMod p, C (w y) * X ^ (-y).val with hfw
  -- Step 1: `T^p - 1 ∣ fx * fw`.
  have hprod : fx * fw = ∑ y : ZMod p, ∑ y' : ZMod p,
      C (x y * w y') * X ^ (y.val + (-y').val) := by
    rw [hfx, hfw, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y' _ => ?_
    rw [C_mul, pow_add]; ring
  have hred : ∑ y : ZMod p, ∑ y' : ZMod p, C (x y * w y') * X ^ ((y - y').val) = 0 := by
    rw [Finset.sum_comm]
    have : ∀ y' : ZMod p, ∑ y : ZMod p, C (x y * w y') * X ^ ((y - y').val)
        = ∑ s : ZMod p, C (x (s + y') * w y') * X ^ s.val := by
      intro y'
      exact (Fintype.sum_equiv (Equiv.addRight y') _ _ (fun s => by simp)).symm
    rw [Finset.sum_congr rfl fun y' _ => this y', Finset.sum_comm]
    have h2 : ∀ s : ZMod p, ∑ y' : ZMod p, C (x (s + y') * w y') * X ^ s.val
        = C (∑ y', x (y' + s) * w y') * X ^ s.val := by
      intro s
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y' _ => by rw [add_comm s y']
    rw [Finset.sum_congr rfl fun s _ => h2 s]
    simp [hcorr]
  have hdvd : (X ^ p - 1 : F[X]) ∣ fx * fw := by
    have : fx * fw = ∑ y : ZMod p, ∑ y' : ZMod p,
        C (x y * w y') * (X ^ (y.val + (-y').val) - X ^ ((y - y').val)) := by
      rw [hprod, ← sub_zero (∑ y : ZMod p, ∑ y' : ZMod p, _), ← hred, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun y' _ => ?_
      ring
    rw [this]
    refine Finset.dvd_sum fun y _ => Finset.dvd_sum fun y' _ => Dvd.dvd.mul_left ?_ _
    have hval : (y - y').val = (y.val + (-y').val) % p := by
      rw [sub_eq_add_neg, ZMod.val_add]
    rw [hval]
    exact X_pow_sub_X_pow_mod_dvd _
  -- Step 2: `T^p - 1 = (T - 1)^p`.
  have hchar : (X ^ p - 1 : F[X]) = (X - C 1) ^ p := by
    rw [map_one, sub_pow_char, one_pow]
  rw [hchar] at hdvd
  -- Step 3: `T - 1 ∤ fx`.
  have hndvd : ¬ (X - C 1) ∣ fx := by
    rw [dvd_iff_isRoot, IsRoot, hfx, eval_finsetSum]
    simpa using hx
  have hw : (X - C (1 : F)) ^ p ∣ fw :=
    (prime_X_sub_C (1 : F)).pow_dvd_of_dvd_mul_left p hndvd hdvd
  -- Step 4: degree.
  have hdeg : fw.natDegree < ((X - C (1 : F)) ^ p).natDegree := by
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
    have hp1 : 0 < p := hp.out.pos
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := p - 1) fun y _ => ?_) ?_
    · refine (natDegree_C_mul_X_pow_le _ _).trans ?_
      have := ZMod.val_lt (-y)
      omega
    · omega
  have hfw0 : fw = 0 := eq_zero_of_dvd_of_natDegree_lt hw hdeg
  have hcoeff : fw.coeff (-y).val = w y := by
    rw [hfw, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single y]
    · simp
    · intro b _ hb
      rw [ite_eq_right_iff]
      intro h
      exact absurd (neg_injective (ZMod.val_injective p h.symm)) hb
    · simp
  rw [← hcoeff, hfw0, coeff_zero]

end OAI.CirculantHadamard.TheoremS
