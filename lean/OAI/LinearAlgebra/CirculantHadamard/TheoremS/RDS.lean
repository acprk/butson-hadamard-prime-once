import OAI.LinearAlgebra.CirculantHadamard.TheoremS.Main

/-!
# Non-split RDS corollary of Theorem S (Corollary R)

`π : G →+ Q` with kernel `N`, `σ : Q → G` a section (so `D = range σ` meets every `N`-coset
exactly once: a semiregular RDS is exactly such a transversal).  RDS condition: every `g ∉ N`
is a difference `σ q₁ - σ q₂` exactly `lam` times.  If some prime `p` satisfies `p ∥ |Q|` and
`N` contains a nonzero element of order prime to `p` (i.e. `N` is not a `p`-group), then no such
`σ` exists.  No splitting hypothesis on `N`, no hypothesis `p ∤ |N|`.
-/

open ComplexConjugate Finset

namespace OAI.CirculantHadamard.TheoremS.RDSCheck

variable {G Q : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [AddCommGroup Q] [Fintype Q] [DecidableEq Q]

lemma fiber_sum_eq_zero (π : G →+ Q) (φ : AddChar G ℂ) (x : G) (hx : π x = 0) (hφ : φ x ≠ 1)
    (s : Q) : ∑ g ∈ univ.filter (fun g => π g = s), φ g = 0 := by
  set S := ∑ g ∈ univ.filter (fun g => π g = s), φ g with hS
  have key : φ x * S = S := by
    rw [hS, mul_sum]
    refine Finset.sum_nbij' (fun g => g + x) (fun g => g - x) ?_ ?_ ?_ ?_ ?_
    · intro g hg; simp only [mem_filter, mem_univ, true_and] at hg ⊢; simp [map_add, hg, hx]
    · intro g hg; simp only [mem_filter, mem_univ, true_and] at hg ⊢; simp [map_sub, hg, hx]
    · intro g _; simp
    · intro g _; simp
    · intro g _; rw [AddChar.map_add_eq_mul, mul_comm]
  have : (φ x - 1) * S = 0 := by rw [sub_mul, key, one_mul, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hφ
  · exact h

theorem no_semiregular_rds (π : G →+ Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q) (lam : ℕ)
    (hrds : ∀ g, π g ≠ 0 → (univ.filter (fun z : Q × Q => σ z.1 - σ z.2 = g)).card = lam)
    (p : ℕ) (hp : p.Prime) (hpQ : p ∣ Fintype.card Q) (hp2 : ¬ p ^ 2 ∣ Fintype.card Q)
    (x : G) (hx0 : x ≠ 0) (hxN : π x = 0) (hxp : ¬ p ∣ addOrderOf x) : False := by
  classical
  obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (a := x)).mpr hx0
  set M := Fintype.card G with hM
  have hM0 : M ≠ 0 := Fintype.card_ne_zero
  set P := ordProj[p] M
  set h := ordCompl[p] M
  have hPh : P * h = M := Nat.ordProj_mul_ordCompl_eq_self M p
  have hph : ¬ p ∣ h := Nat.not_dvd_ordCompl hp hM0
  set φ : AddChar G ℂ := ψ ^ P
  -- φ is nontrivial at x
  have hφx : φ x ≠ 1 := by
    intro h1
    have hx1 : ψ x ^ P = 1 := by simpa [φ] using h1
    have hxk : ψ x ^ addOrderOf x = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, addOrderOf_nsmul_eq_zero, AddChar.map_zero_eq_one]
    have hcop : Nat.Coprime P (addOrderOf x) := by
      have : Nat.Coprime (p ^ (M.factorization p)) (addOrderOf x) :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hxp)
      simpa [P] using this
    have : ψ x ^ (Nat.gcd P (addOrderOf x)) = 1 :=
      (pow_gcd_eq_one.mpr ⟨hx1, hxk⟩)
    rw [hcop, pow_one] at this
    exact hψ this
  -- the twisted transversal a : Q → μ_h
  let a : Q → ℂ := fun q => φ (σ q)
  have ha : ∀ q, a q ^ h = 1 := by
    intro q
    simp only [a, φ, AddChar.pow_apply, ← pow_mul, hPh]
    rw [← AddChar.map_nsmul_eq_pow, hM, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
  have hconj : ∀ g, conj (φ g) = φ (-g) := by
    intro g
    have h1 : φ g * conj (φ g) = 1 :=
      norm_mul_conj_eq_one (h := M) hM0 (by
        rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one])
    have h2 : φ g * φ (-g) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel,
      AddChar.map_zero_eq_one]
    have hne : φ g ≠ 0 := left_ne_zero_of_mul_eq_one h1
    exact mul_left_cancel₀ hne (h1.trans h2.symm)
  have hperf : ∀ s ≠ 0, ∑ q, a (q + s) * conj (a q) = 0 := by
    intro s hs
    have step1 : ∀ q, a (q + s) * conj (a q) = φ (σ (q + s) - σ q) := by
      intro q; simp only [a]; rw [hconj, ← AddChar.map_add_eq_mul, sub_eq_add_neg]
    simp_rw [step1]
    -- group by the value of the difference
    rw [← Finset.sum_fiberwise (s := univ) (g := fun q => σ (q + s) - σ q)
      (f := fun q => φ (σ (q + s) - σ q))]
    have step2 : ∀ g : G, (∑ q ∈ univ.filter (fun q => σ (q + s) - σ q = g),
        φ (σ (q + s) - σ q)) = (if π g = s then (lam : ℂ) * φ g else 0) := by
      intro g
      rw [Finset.sum_congr rfl (fun q hq => by rw [(mem_filter.mp hq).2])]
      rw [sum_const, nsmul_eq_mul]
      split_ifs with hg
      · congr 1
        have hg0 : π g ≠ 0 := hg ▸ hs
        rw [← hrds g hg0]
        norm_cast
        have key : ∀ z : Q × Q, σ z.1 - σ z.2 = g → z.1 = z.2 + s := by
          intro z hz
          have := congrArg π hz
          rw [map_sub, hσ, hσ, hg] at this
          rw [← this]; abel
        refine Finset.card_nbij' (fun q => (q + s, q)) (fun z => z.2) ?_ ?_ ?_ ?_
        · intro q hq
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hq ⊢
          exact hq
        · intro z hz
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hz ⊢
          rw [← key z hz]; exact hz
        · intro q _; rfl
        · intro z hz
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hz
          have := key z hz
          ext <;> simp [this]
      · have : univ.filter (fun q => σ (q + s) - σ q = g) = ∅ := by
          ext q
          simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
          intro hq
          apply hg
          rw [← hq, map_sub, hσ, hσ]; abel
        rw [this, card_empty, Nat.cast_zero, zero_mul]
    rw [Finset.sum_congr rfl (fun g _ => step2 g), ← Finset.sum_filter]
    rw [← mul_sum, fiber_sum_eq_zero π φ x hxN hφx s, mul_zero]
  exact no_perfect_function Q h p hp hpQ hp2 hph a ha hperf

end OAI.CirculantHadamard.TheoremS.RDSCheck

#print axioms OAI.CirculantHadamard.TheoremS.RDSCheck.no_semiregular_rds
