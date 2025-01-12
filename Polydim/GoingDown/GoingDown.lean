import Mathlib

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The going-down theorem for flat algebras. -/
lemma exists_isPrime_and_liesOver_of_isPrime_of_le_of_liesOver [Module.Flat A B] (p p' : Ideal A)
    [p.IsPrime] [p'.IsPrime]
    (hle : p ≤ p') (P' : Ideal B) [P'.IsPrime] [P'.LiesOver p'] :
    ∃ (P : Ideal B), P.IsPrime ∧ P.LiesOver p :=
  sorry
