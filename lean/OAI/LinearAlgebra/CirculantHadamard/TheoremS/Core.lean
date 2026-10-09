import OAI.LinearAlgebra.CirculantHadamard.TheoremS.LocalRing

/-!
# Theorem S, abstract core (ring-theoretic part)

Let `O` be a commutative ring and `P` a maximal ideal containing the prime `p`.  Suppose we are
given a finite family (indexed by `T`, in the application: characters of `H`) of pairs of
`C_p`-sequences `x t, w t : ZMod p → O` (in the application: `X_χ` and `X_χ^♯`), such that

* `∑_y x t (y + s) * w t y = N` if `s = 0` and `0` otherwise, where `N = p * M`
  (this is `X_χ X_χ^♯ = |G|`);
* `p * M ∉ P ^ 2` (`p` is unramified at `P` and `M ∉ P`);
* `∑_t x t 0 * w t 0 = M * M` and `M * M ∉ P` (Parseval over `Ĥ` at the coset `y = 0`).

Then we get a contradiction.
-/

namespace OAI.CirculantHadamard.TheoremS

open Finset

variable {O : Type*} [CommRing O] {p : ℕ} [hp : Fact p.Prime]

/-- Summing the correlation over all shifts gives the product of the augmentations. -/
lemma sum_mul_sum_eq_sum_corr (x w : ZMod p → O) :
    (∑ y, x y) * (∑ y, w y) = ∑ s, ∑ y, x (y + s) * w y := by
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  rw [Finset.sum_comm (f := fun s y => x (y + s) * w y)]
  refine Finset.sum_congr rfl fun y' _ => ?_
  exact (Fintype.sum_equiv (Equiv.addLeft y') (fun s => x (y' + s) * w y')
    (fun s => x s * w y') (fun s => rfl)).symm

/-- Correlation of `(w, x)` at `s` equals the correlation of `(x, w)` at `-s`. -/
lemma corr_swap (x w : ZMod p → O) (s : ZMod p) :
    ∑ y, w (y + s) * x y = ∑ y, x (y + -s) * w y := by
  refine Fintype.sum_equiv (Equiv.addRight s) _ _ (fun y => ?_)
  simp [mul_comm]

/-- From `X X^♯ ≡ 0` in `(O/P)[C_p]` and the fact that not both augmentations lie in `P`,
every product `x y * w y` lies in `P`. -/
theorem mul_mem_of_corr (P : Ideal O) [P.IsMaximal] (hpP : (p : O) ∈ P)
    (x w : ZMod p → O) (hcorr : ∀ s, ∑ y, x (y + s) * w y ∈ P)
    (hnot : ¬ ((∑ y, x y) ∈ P ∧ (∑ y, w y) ∈ P)) (y : ZMod p) :
    x y * w y ∈ P := by
  let _ : Field (O ⧸ P) := Ideal.Quotient.field P
  have _ : CharP (O ⧸ P) p := by
    rw [CharP.charP_iff_prime_eq_zero hp.out, ← map_natCast (Ideal.Quotient.mk P),
      Ideal.Quotient.eq_zero_iff_mem]
    exact hpP
  let π := Ideal.Quotient.mk P
  have hc : ∀ s, ∑ y, π (x (y + s)) * π (w y) = 0 := fun s => by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr (hcorr s)
    simpa [π, map_sum, map_mul] using this
  by_cases hx : (∑ y, x y) ∈ P
  · have hw : (∑ y, w y) ∉ P := fun hw => hnot ⟨hx, hw⟩
    have hc' : ∀ s, ∑ y, π (w (y + s)) * π (x y) = 0 := fun s =>
      (corr_swap (fun y => π (x y)) (fun y => π (w y)) s).trans (hc (-s))
    have hsum : ∑ y, π (w y) ≠ 0 := by
      rw [← map_sum]
      exact fun h => hw (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have := eq_zero_of_corr_eq_zero (fun y => π (w y)) (fun y => π (x y)) hc' hsum y
    exact P.mul_mem_right _ (Ideal.Quotient.eq_zero_iff_mem.mp this)
  · have hsum : ∑ y, π (x y) ≠ 0 := by
      rw [← map_sum]
      exact fun h => hx (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have := eq_zero_of_corr_eq_zero (fun y => π (x y)) (fun y => π (w y)) hc hsum y
    exact P.mul_mem_left _ (Ideal.Quotient.eq_zero_iff_mem.mp this)

/-- **Core of Theorem S** (abstract form). -/
theorem core_false {T : Type*} [Fintype T] (P : Ideal O) [P.IsMaximal]
    (hpP : (p : O) ∈ P) (M : ℕ) (hM2 : ((p * M : ℕ) : O) ∉ P ^ 2)
    (hMM : ((M * M : ℕ) : O) ∉ P) (x w : T → ZMod p → O)
    (hcorr : ∀ t s, ∑ y, x t (y + s) * w t y = if s = 0 then ((p * M : ℕ) : O) else 0)
    (hsum : ∑ t, x t 0 * w t 0 = ((M * M : ℕ) : O)) : False := by
  apply hMM
  rw [← hsum]
  refine P.sum_mem fun t _ => ?_
  have hNP : ((p * M : ℕ) : O) ∈ P := by
    rw [Nat.cast_mul]; exact P.mul_mem_right _ hpP
  refine mul_mem_of_corr P hpP (x t) (w t) (fun s => ?_) (fun hboth => ?_) 0
  · rw [hcorr t s]; split_ifs
    · exact hNP
    · exact P.zero_mem
  · apply hM2
    have hprod := sum_mul_sum_eq_sum_corr (x t) (w t)
    simp only [hcorr t, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hprod
    rw [← hprod, pow_two]
    exact Ideal.mul_mem_mul hboth.1 hboth.2

end OAI.CirculantHadamard.TheoremS
