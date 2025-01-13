import Mathlib
import Polydim.Dimension.Height

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [IsNoetherianRing B]

instance (p : Ideal A) [p.IsPrime] : IsNoetherianRing (Localization.AtPrime p) :=
  sorry

-- this needs some more inputs on dimension theory first
lemma ringKrullDim_le_ringKrullDim_add_of_isLocalRing [IsLocalRing A] [IsLocalRing B] :
    ringKrullDim B ≤ ringKrullDim A +
      ringKrullDim (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) :=
  sorry

/-- Matsumura 13.B Th. 19 (1) -/
lemma primeHeight_le_primeHeight_add_of_liesOver (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime]
      [P.LiesOver p] :
    P.primeHeight ≤ p.primeHeight +
      (P.map (Ideal.Quotient.mk <| p.map (algebraMap A B))).primeHeight := by
  let Aₚ := Localization.AtPrime p
  let Bₚ := Localization.AtPrime P
  letI : Algebra Aₚ Bₚ :=
    Localization.localRingHom p P (algebraMap A B) (Ideal.LiesOver.over) |>.toAlgebra
  let BₚQ := Bₚ ⧸ (IsLocalRing.maximalIdeal Aₚ).map (algebraMap Aₚ Bₚ)
  let f : B ⧸ p.map (algebraMap A B) →+*
      Bₚ ⧸ (IsLocalRing.maximalIdeal Aₚ).map (algebraMap Aₚ Bₚ) :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (algebraMap B Bₚ)) <| by
      sorry
  letI : Algebra (B ⧸ p.map (algebraMap A B)) BₚQ := f.toAlgebra
  have : (Ideal.map (Ideal.Quotient.mk (p.map (algebraMap A B))) P).IsPrime := by
    sorry
  have : IsLocalization.AtPrime BₚQ (P.map (Ideal.Quotient.mk (p.map (algebraMap A B)))) :=
    sorry
  rw [← WithBot.coe_le_coe]
  simp only [Ideal.Quotient.algebraMap_eq, WithBot.coe_add]
  rw [Ideal.primeHeight_eq_ringKrullDim, Ideal.primeHeight_eq_ringKrullDim,
    IsLocalization.primeHeight_eq_ringKrullDim (B := BₚQ)]
  exact ringKrullDim_le_ringKrullDim_add_of_isLocalRing

/-- Matsumura 13.B Th. 19 (2) -/
lemma primeHeight_eq_primeHeight_add_of_liesOver_of_flat [Module.Flat A B] (p : Ideal A) [p.IsPrime]
    (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    P.primeHeight = p.primeHeight +
      (P.map (Ideal.Quotient.mk <| p.map (algebraMap A B))).primeHeight :=
  -- use `primeHeight_le_primeHeight_add_of_liesOver` for one direction
  -- and going down for the other one
  sorry
