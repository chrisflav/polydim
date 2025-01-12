import Mathlib

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [IsNoetherianRing B]

-- TODO: replace by better definition
/-- The height of a prime ideal in a ring is the supremum over the lengths of prime ideal
chains ending at `p`. -/
noncomputable def Ideal.primeHeight (p : Ideal A) : WithTop ℕ :=
  Set.chainHeight { q : Ideal A | q.IsPrime ∧ q < p }

/-- The height of a prime ideal `p` equals to the dimension of `A` localized away from `p`. -/
lemma Ideal.primeHeight_eq_ringKrullDim (p : Ideal A) [p.IsPrime] :
    p.primeHeight = ringKrullDim (Localization.AtPrime p) :=
  sorry

/-- Matsumura 13.B Th. 19 (1) -/
lemma primeHeight_le_primeHeight_add_of_liesOver (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime]
      [P.LiesOver p] :
    P.primeHeight ≤ p.primeHeight +
      (Ideal.map (algebraMap B <| B ⧸ Ideal.map (algebraMap A B) p) P).primeHeight :=
  sorry

/-- Matsumura 13.B Th. 19 (2) -/
lemma primeHeight_eq_primeHeight_add_of_liesOver_of_flat (p : Ideal A) [p.IsPrime] (P : Ideal B)
    [P.IsPrime] [P.LiesOver p] :
    P.primeHeight = p.primeHeight +
      (Ideal.map (algebraMap B <| B ⧸ Ideal.map (algebraMap A B) p) P).primeHeight :=
  sorry
