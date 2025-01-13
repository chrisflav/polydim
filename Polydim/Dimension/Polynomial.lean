import Mathlib
import Polydim.Dimension.Homomorphism

variable {A : Type*} [CommRing A]

open Polynomial

-- for some reason this is missing in mathlib, but we have the existence of a basis
instance : Module.Free A A[X] := sorry

/-- `(A ⧸ I)[X]` is isomorphic to `A[X] / I`. -/
def polynomialQuotient (I : Ideal A) :
    (A[X] ⧸ (I.map <| algebraMap A A[X])) ≃ₐ[A] (A ⧸ I)[X] :=
  sorry

/-- Let `p` be a prime ideal of `A`. If `P` is a prime ideal of `A[X]` maximal
among the prime ideals lying over `p`, `ht(P) = ht(p) + 1`. -/
lemma Ideal.primeHeight_polynomial_of_isMaximal [IsNoetherianRing A] (p : Ideal A)
    [p.IsMaximal] (P : Ideal A[X]) [P.IsMaximal] [P.LiesOver p] :
    P.primeHeight = p.primeHeight + 1 := by
  have : (Ideal.map (algebraMap A[X] <|
      A[X] ⧸ Ideal.map (algebraMap A A[X]) p) P).primeHeight = 1 := by
    let e : (A[X] ⧸ Ideal.map (algebraMap A A[X]) p) ≃+* (A ⧸ p)[X] :=
      polynomialQuotient p
    let P' : Ideal (A ⧸ p)[X] :=
      Ideal.map e <| Ideal.map (algebraMap A[X] <| A[X] ⧸ Ideal.map (algebraMap A A[X]) p) P
    -- use that `P'` is a maximal ideal of `(A ⧸ p)[X]`
    have : P'.primeHeight = 1 :=
      sorry
    have : (map (algebraMap A[X] (A[X] ⧸ map (algebraMap A A[X]) p)) P).IsPrime :=
      sorry
    simp only [P'] at this
    rwa [← height_eq_of_ringEquiv e <|
      Ideal.map (algebraMap A[X] <| A[X] ⧸ Ideal.map (algebraMap A A[X]) p) P]
  rw [primeHeight_eq_primeHeight_add_of_liesOver_of_flat p, this]

/-- Let `p` be a prime ideal of `A`. If `P` is a prime ideal of `A[X]` maximal
among the prime ideals lying over `p`, `ht(P) = ht(p) + 1`. -/
lemma Ideal.primeHeight_polynomial [IsNoetherianRing A] (p : Ideal A)
    [p.IsPrime] (P : Ideal A[X]) [P.IsMaximal] [P.LiesOver p] :
    P.primeHeight = p.primeHeight + 1 := by
  let Aₚ := Localization.AtPrime p
  let Bₚ := Localization (Submonoid.map (algebraMap A A[X]) <| p.primeCompl)
  -- use `IsLocalization.height_eq_of_disjoint`
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
  rw [← hP, Ideal.primeHeight_polynomial p P]
  sorry

/-- `dim A[X] = dim A + 1` if `A` is Noetherian. -/
theorem ringKrullDim_polynomial [IsNoetherianRing A] :
    ringKrullDim A[X] = ringKrullDim A + 1 := by
  apply le_antisymm
  exact ringKrullDim_polynomial_le
  exact le_ringKrullDim_polynomial
