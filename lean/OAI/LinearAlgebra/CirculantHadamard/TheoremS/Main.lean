import OAI.LinearAlgebra.CirculantHadamard.TheoremS.Product
import OAI.LinearAlgebra.CirculantHadamard.TheoremS.Decomposition

/-!
# Theorem S (main statements)

**Theorem S.**  Let `G` be a finite abelian group, `p` a prime with `p ∥ |G|`, and `p ∤ h`.
Then there is no group-invariant Butson Hadamard matrix over `μ_h` indexed by `G`, i.e. no
`a : G → ℂ` with `a g ^ h = 1` for all `g` and perfect autocorrelation
`∑_g a(g + s) * conj (a g) = 0` for every `s ≠ 0`.  (Perfect autocorrelation is the coefficient
form of `X X^* = |G|` in `ℂ[G]`, where `X = ∑ a(g) g`.)

We give the general abelian statement, the cyclic statement (perfect sequences), and the
quaternary corollary.
-/

namespace OAI.CirculantHadamard.TheoremS

open ComplexConjugate

/-- Perfect autocorrelation is transported along an additive isomorphism. -/
lemma perfect_transfer {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] [Fintype G]
    [Fintype G'] (e : G ≃+ G') (a : G → ℂ)
    (hperf : ∀ s ≠ 0, ∑ g, a (g + s) * conj (a g) = 0) :
    ∀ s ≠ 0, ∑ g', a (e.symm (g' + s)) * conj (a (e.symm g')) = 0 := by
  intro s hs
  have hs' : e.symm s ≠ 0 := by simpa using hs
  rw [← hperf (e.symm s) hs']
  exact Fintype.sum_equiv e.symm.toEquiv _ _ (fun g' => by simp [map_add])

/-- **Theorem S (finite abelian groups).**  If `p` is prime, `p ∣ |G|`, `p² ∤ |G|` and `p ∤ h`,
there is no `μ_h`-valued function on `G` with perfect autocorrelation. -/
theorem no_perfect_function (G : Type*) [AddCommGroup G] [Fintype G] (h p : ℕ)
    (hp : p.Prime) (hpG : p ∣ Fintype.card G) (hp2 : ¬ p ^ 2 ∣ Fintype.card G)
    (hph : ¬ p ∣ h) (a : G → ℂ) (ha : ∀ g, a g ^ h = 1)
    (hperf : ∀ s ≠ 0, ∑ g, a (g + s) * conj (a g) = 0) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  rw [← Nat.card_eq_fintype_card] at hpG hp2
  obtain ⟨B, hB, ⟨e⟩⟩ := exists_addEquiv_zmod_prod p hpG hp2
  have : Fintype B := Fintype.ofFinite B
  rw [Nat.card_eq_fintype_card] at hB
  exact no_perfect_prod B hB h hph (fun g => a (e.symm g)) (fun g => ha _)
    (perfect_transfer e a hperf)

/-- **Theorem S, cyclic case (perfect sequences).**  If `p` is prime with `p ∥ n` and `p ∤ h`,
there is no perfect sequence of length `n` over the `h`-th roots of unity. -/
theorem no_perfect_sequence (n h p : ℕ) [NeZero n] (hp : p.Prime) (hpn : p ∣ n)
    (hp2 : ¬ p ^ 2 ∣ n) (hph : ¬ p ∣ h) (a : ZMod n → ℂ) (ha : ∀ x, a x ^ h = 1)
    (hperf : ∀ s ≠ 0, ∑ x, a (x + s) * conj (a x) = 0) : False :=
  no_perfect_function (ZMod n) h p hp (by rwa [ZMod.card]) (by rwa [ZMod.card]) hph a ha hperf

/-- **Corollary (quaternary sequences).**  There is no perfect quaternary sequence (values in
`{±1, ±i}`) of length `N` if some odd prime `p` satisfies `v_p(N) = 1`. -/
theorem no_perfect_quaternary_sequence (N p : ℕ) [NeZero N] (hp : p.Prime) (hodd : p ≠ 2)
    (hpN : p ∣ N) (hp2 : ¬ p ^ 2 ∣ N) (a : ZMod N → ℂ) (ha : ∀ x, a x ^ 4 = 1)
    (hperf : ∀ s ≠ 0, ∑ x, a (x + s) * conj (a x) = 0) : False := by
  refine no_perfect_sequence N 4 p hp hpN hp2 ?_ a ha hperf
  intro h4
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact h4)
  exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

end OAI.CirculantHadamard.TheoremS
