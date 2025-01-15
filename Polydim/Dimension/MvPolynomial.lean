import Polydim.Dimension.Polynomial

lemma MvPolynomial.ringKrullDim_aux {R : Type*} [CommRing R] [IsNoetherianRing R]
    (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) R) = ringKrullDim R + n := by
  induction' n with n ih
  · -- use `MvPolynomial.pUnitAlgEquiv` and `MvPolynomial.renameEquiv`
    rw [CharP.cast_eq_zero, add_zero, ringKrullDim_eq_of_ringEquiv (isEmptyRingEquiv R (Fin 0))]
  · -- use `MvPolynomial.finSuccEquiv`
    rw [ringKrullDim_eq_of_ringEquiv <| AlgEquiv.toRingEquiv <| MvPolynomial.finSuccEquiv R n,
      ringKrullDim_polynomial, ih, Nat.cast_add, Nat.cast_one, add_assoc]

lemma MvPolynomial.ringKrullDim_eq_ringKrullDim_add {R : Type*} [CommRing R] [IsNoetherianRing R]
    {ι : Type*} [Finite ι] :
    ringKrullDim (MvPolynomial ι R) = ringKrullDim R + Nat.card ι := by
  letI : Fintype ι := Fintype.ofFinite ι
  let e := AlgEquiv.toRingEquiv <| MvPolynomial.renameEquiv R <| Fintype.equivFin ι
  rw [ringKrullDim_eq_of_ringEquiv e, MvPolynomial.ringKrullDim_aux]
  rw [Nat.card_eq_fintype_card]
  -- use `MvPolynomial.renameEquiv`

#check Order.krullDim_le_of_strictMono
#check MvPolynomial.rename
#check MvPolynomial.rename_injective
#check Polynomial.quotientSpanXSubCAlgEquiv
#check MvPolynomial.sumAlgEquiv

noncomputable def weg {ι : Type*} [Infinite ι] : ℕ → ι := Infinite.natEmbedding ι



def liuwegf {R : Type*} [Field R] [IsNoetherianRing R]
    [Nontrivial R] {ι : Type*} [Infinite ι] : ℕ → PrimeSpectrum (MvPolynomial ι R) := sorry

lemma MvPolynomial.ringKrullDim_eq_top_of_infinite {R : Type*} [CommRing R] [IsNoetherianRing R]
    [Nontrivial R] {ι : Type*} [Infinite ι] :
    ringKrullDim (MvPolynomial ι R) = ⊤ := by
  wlog hisfield : IsField R with hwhenfield
  · -- `R` is non-trivial so it has a maximal ideal `m`
    obtain ⟨m, hm⟩ := Ideal.exists_maximal R
    suffices heqtop : ringKrullDim ((MvPolynomial ι R) ⧸ Ideal.map MvPolynomial.C m) = ⊤
    · exact eq_top_mono (ringKrullDim_quotient_le <| Ideal.map MvPolynomial.C m) heqtop
    · let e := AlgEquiv.toRingEquiv <| MvPolynomial.quotientEquivQuotientMvPolynomial (σ := ι) m
      rw [ringKrullDim_eq_of_ringEquiv e.symm]
      exact hwhenfield <| (Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp hm
    -- now quotient out by the maximal ideal `R ⧸ m`, use
    -- `MvPolynomial.quotientEquivQuotientMvPolynomial`
  -- now the ideals `(X_1, X_2, ..., X_i)` are prime ideals of `MvPolynomial ι R`
  -- and form an infinite chain
  · rw [ringKrullDim]
    sorry
