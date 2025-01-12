import Mathlib
import Polydim.Dimension.Homomorphism

section

variable {A : Type*} [CommRing A]

/-- `dim A ≤ n` if and only if the height of all prime ideals is less than `n`. -/
lemma ringKrullDim_le_of_height_le [Nontrivial A] (n : WithBot (WithTop ℕ)) :
  ringKrullDim A ≤ n ↔
    ∀ (p : Ideal A), p.IsPrime → p.primeHeight ≤ n :=
  sorry

lemma Ideal.exists_isMaximal_height_eq_of_nontrivial [Nontrivial A] :
    ∃ (p : Ideal A), p.IsMaximal ∧ p.primeHeight = ringKrullDim A :=
  sorry

end

variable {A : Type*} [CommRing A]

open Polynomial

/-- Let `p` be a prime ideal of `A`. If `P` is a prime ideal of `A[X]` maximal
among the prime ideals lying over `p`, `ht(P) = ht(p) + 1`. -/
lemma Ideal.primeHeight_polynomial [IsNoetherianRing A] (p : Ideal A)
    [p.IsPrime] (P : Ideal A[X]) [P.IsMaximal] [P.LiesOver p] :
    P.primeHeight = p.primeHeight + 1 := by
  sorry

lemma Ideal.exists_ideal_liesOver_polynomial_of_isPrime (p : Ideal A)
    [p.IsPrime] : ∃ (P : Ideal A[X]), P.IsPrime ∧ P.LiesOver p :=
  sorry

lemma le_ringKrullDim_polynomial [IsNoetherianRing A] :
    ringKrullDim A + 1 ≤ ringKrullDim A[X] := by
  nontriviality A
  obtain ⟨p, _, hp⟩ := Ideal.exists_isMaximal_height_eq_of_nontrivial (A := A)
  rw [← hp]
  obtain ⟨P, _, hP⟩ := Ideal.exists_ideal_liesOver_polynomial_of_isPrime p
  have : ∃ Q : Ideal A[X], Q.IsMaximal ∧ P ≤ Q := sorry
  obtain ⟨Q, _, hPQ⟩ := this
  have : Q.LiesOver p := sorry
  have : Q.primeHeight = p.primeHeight + 1 :=
    p.primeHeight_polynomial Q
  sorry

lemma ringKrullDim_polynomial_le [IsNoetherianRing A] :
    ringKrullDim A[X] ≤ ringKrullDim A + 1 := by
  nontriviality A[X]
  obtain ⟨P, _, hP⟩ := Ideal.exists_isMaximal_height_eq_of_nontrivial (A := A[X])
  let p : Ideal A := P.comap (algebraMap A A[X])
  rw [← hP]
  rw [Ideal.primeHeight_polynomial p P]
  sorry

/-- `dim A[X] = dim A + 1` if `A` is Noetherian. -/
theorem ringKrullDim_polynomial [IsNoetherianRing A] :
    ringKrullDim A[X] = ringKrullDim A + 1 := by
  apply le_antisymm
  exact ringKrullDim_polynomial_le
  exact le_ringKrullDim_polynomial
