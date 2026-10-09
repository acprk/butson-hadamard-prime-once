import Mathlib

/-!
# Theorem S, group theory: `G ≃ C_p × H` when `p ∥ |G|`

If `G` is a finite abelian group and `p` is a prime with `p ∣ |G|` and `p² ∤ |G|`, then
`G ≃+ ZMod p × B` for a subgroup `B` with `p ∤ |B|`.  We take `A = G[p]` (the `p`-torsion) and
`B = G[m]` where `|G| = p m`; Bézout `u p + v m = 1` splits `G = A ⊕ B`, Cauchy's theorem
gives `|A| = p`, and a group of prime order is cyclic.
-/

namespace OAI.CirculantHadamard.TheoremS

variable (G : Type*) [AddCommGroup G]

/-- The `k`-torsion subgroup `{g | k • g = 0}` (`k : ℤ`). -/
def torsionZ (k : ℤ) : AddSubgroup G where
  carrier := {g | k • g = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [zsmul_add, ha, hb, add_zero]
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [zsmul_neg, ha, neg_zero]

variable {G}

lemma mem_torsionZ {k : ℤ} {g : G} : g ∈ torsionZ G k ↔ k • g = 0 := Iff.rfl

/-- An element of the `k`-torsion subgroup (`k : ℕ`) has additive order dividing `k`. -/
lemma addOrderOf_dvd_of_mem_torsionZ {k : ℕ} (x : torsionZ G k) : addOrderOf x ∣ k := by
  apply addOrderOf_dvd_of_nsmul_eq_zero
  apply Subtype.ext
  have := x.2
  rw [mem_torsionZ, natCast_zsmul] at this
  simpa using this

/-- **Splitting off the `p`-part.** -/
theorem exists_addEquiv_zmod_prod [Finite G] (p : ℕ) [hp : Fact p.Prime]
    (hpn : p ∣ Nat.card G) (hp2 : ¬ p ^ 2 ∣ Nat.card G) :
    ∃ B : AddSubgroup G, ¬ p ∣ Nat.card B ∧ Nonempty (G ≃+ ZMod p × B) := by
  classical
  obtain ⟨m, hm⟩ := hpn
  have hpm : ¬ p ∣ m := by
    rintro ⟨k, rfl⟩
    exact hp2 ⟨k, by rw [hm]; ring⟩
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  set A := torsionZ G p
  set B := torsionZ G m
  have hcard : ∀ g : G, ((p * m : ℕ) : ℤ) • g = 0 := by
    intro g
    rw [natCast_zsmul, ← hm]
    exact card_nsmul_eq_zero'
  let f : A × B →+ G := A.subtype.coprod B.subtype
  have hf : ∀ x : A × B, f x = (x.1 : G) + x.2 := fun x => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    rw [hf] at hab
    have hab' : (a : G) = -b := eq_neg_of_add_eq_zero_left hab
    have ha1 : (p : ℤ) • (a : G) = 0 := a.2
    have ha2 : (m : ℤ) • (a : G) = 0 := by rw [hab', zsmul_neg, (mem_torsionZ.mp b.2), neg_zero]
    have ha0 : (a : G) = 0 := by
      calc (a : G) = (u * p + v * m : ℤ) • (a : G) := by rw [huv, one_zsmul]
        _ = u • ((p : ℤ) • (a : G)) + v • ((m : ℤ) • (a : G)) := by
          rw [add_zsmul, mul_zsmul, mul_zsmul]
        _ = 0 := by rw [ha1, ha2, zsmul_zero, zsmul_zero, add_zero]
    have hb0 : (b : G) = 0 := by rw [← neg_eq_zero, ← hab', ha0]
    exact Prod.ext (Subtype.ext ha0) (Subtype.ext hb0)
  have hsurj : Function.Surjective f := by
    intro g
    refine ⟨(⟨(v * m : ℤ) • g, ?_⟩, ⟨(u * p : ℤ) • g, ?_⟩), ?_⟩
    · rw [mem_torsionZ, ← mul_zsmul, show (p : ℤ) * (v * m) = v * ((p * m : ℕ) : ℤ) by
        push_cast; ring, mul_zsmul, hcard, zsmul_zero]
    · rw [mem_torsionZ, ← mul_zsmul, show (m : ℤ) * (u * p) = u * ((p * m : ℕ) : ℤ) by
        push_cast; ring, mul_zsmul, hcard, zsmul_zero]
    · rw [hf]
      simp only
      rw [← add_zsmul, add_comm, huv, one_zsmul]
  let e : A × B ≃+ G := AddEquiv.ofBijective f ⟨hinj, hsurj⟩
  have hprod : Nat.card A * Nat.card B = p * m := by
    rw [← Nat.card_prod, Nat.card_congr e.toEquiv, hm]
  -- `p ∤ |B|`
  have hB : ¬ p ∣ Nat.card B := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hdvd
    exact hpm (hx ▸ addOrderOf_dvd_of_mem_torsionZ x)
  -- `|A| = p`
  have hpA : p ∣ Nat.card A := by
    have : p ∣ Nat.card A * Nat.card B := hprod ▸ dvd_mul_right p m
    exact (hp.out.dvd_mul.mp this).resolve_right hB
  have hAm : Nat.Coprime (Nat.card A) m := by
    apply Nat.coprime_of_dvd
    intro q hq hqA hqm
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' q hqA
    have hqp : q ∣ p := hx ▸ addOrderOf_dvd_of_mem_torsionZ x
    rw [(Nat.prime_dvd_prime_iff_eq hq hp.out).mp hqp] at hqm
    exact hpm hqm
  have hAp : Nat.card A ∣ p := hAm.dvd_of_dvd_mul_right ⟨Nat.card B, hprod.symm⟩
  have hA : Nat.card A = p := by
    rcases (Nat.dvd_prime hp.out).mp hAp with h1 | h1
    · rw [h1] at hpA
      exact absurd (Nat.le_of_dvd one_pos hpA) (by have := hp.out.one_lt; omega)
    · exact h1
  have hcyc : IsAddCyclic A := isAddCyclic_of_prime_card hA
  let eA : ZMod p ≃+ A :=
    (ZMod.ringEquivCongr hA.symm).toAddEquiv.trans (zmodAddCyclicAddEquiv hcyc)
  exact ⟨B, hB, ⟨e.symm.trans (eA.symm.prodCongr (AddEquiv.refl B))⟩⟩

end OAI.CirculantHadamard.TheoremS
