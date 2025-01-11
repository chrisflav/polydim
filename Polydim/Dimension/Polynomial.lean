import Mathlib

/-- `dim A[X] = dim A + 1` if `A` is Noetherian. -/
theorem ringKrullDim_polynomial (A : Type*) [CommRing A] [IsNoetherianRing A] :
    ringKrullDim (Polynomial A) = ringKrullDim A + 1 :=
  sorry
