import Mathlib
import Polydim.Dimension.Height
import Polydim.Dimension.NoetherianLocal

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- Matsumura 13.B Th. 19 (2) -/
lemma primeHeight_eq_primeHeight_add_of_liesOver_of_flat [Module.Flat A B] (p : Ideal A) [p.IsPrime]
    (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    P.primeHeight = p.primeHeight +
      (P.map (Ideal.Quotient.mk <| p.map (algebraMap A B))).primeHeight :=
  -- use `primeHeight_le_primeHeight_add_of_liesOver` for one direction
  -- and going down for the other one
  sorry
