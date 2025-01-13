import Mathlib
import Polydim.Dimension.Height

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [IsNoetherianRing B]

-- this needs some more inputs on dimension theory first
lemma ringKrullDim_le_ringKrullDim_add_of_isLocalRing [IsLocalRing A] [IsLocalRing B] :
    ringKrullDim B ≤ ringKrullDim A +
      ringKrullDim (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) :=
  sorry

/-- Matsumura 13.B Th. 19 (1) -/
lemma primeHeight_le_primeHeight_add_of_liesOver (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime]
      [P.LiesOver p] :
    P.primeHeight ≤ p.primeHeight +
      (Ideal.map (algebraMap B <| B ⧸ Ideal.map (algebraMap A B) p) P).primeHeight := by
  sorry

/-- Matsumura 13.B Th. 19 (2) -/
lemma primeHeight_eq_primeHeight_add_of_liesOver_of_flat [Module.Flat A B] (p : Ideal A) [p.IsPrime]
    (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    P.primeHeight = p.primeHeight +
      (Ideal.map (algebraMap B <| B ⧸ Ideal.map (algebraMap A B) p) P).primeHeight :=
  -- use `primeHeight_le_primeHeight_add_of_liesOver` for one direction
  -- and going down for the other one
  sorry
