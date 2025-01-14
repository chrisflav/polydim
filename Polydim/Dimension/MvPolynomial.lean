import Polydim.Dimension.Polynomial

lemma MvPolynomial.ringKrullDim_aux {R : Type*} [CommRing R] [IsNoetherianRing R]
    (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) R) = ringKrullDim R + n := by
  induction' n with n ih
  · -- use `MvPolynomial.pUnitAlgEquiv` and `MvPolynomial.renameEquiv`
    sorry
  · -- use `MvPolynomial.finSuccEquiv`
    sorry

lemma MvPolynomial.ringKrullDim_eq_ringKrullDim_add {R : Type*} [CommRing R] [IsNoetherianRing R]
    {ι : Type*} [Finite ι] :
    ringKrullDim (MvPolynomial ι R) = ringKrullDim R + Nat.card ι :=
  letI : Fintype ι := Fintype.ofFinite ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  -- use `MvPolynomial.renameEquiv`
  sorry

lemma MvPolynomial.ringKrullDim_eq_top_of_infinite {R : Type*} [CommRing R] [IsNoetherianRing R]
    [Nontrivial R] {ι : Type*} [Infinite ι] :
    ringKrullDim (MvPolynomial ι R) = ⊤ := by
  wlog h : IsField R
  · -- `R` is non-trivial so it has a maximal ideal `m`
    obtain ⟨m, hm⟩ := Ideal.exists_maximal R
    -- now quotient out by the maximal ideal `R ⧸ m`, use
    -- `MvPolynomial.quotientEquivQuotientMvPolynomial`
    sorry
  -- now the ideals `(X_1, X_2, ..., X_i)` are prime ideals of `MvPolynomial ι R`
  -- and form an infinite chain
  sorry
