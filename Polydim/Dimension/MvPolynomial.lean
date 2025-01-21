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

section

open MvPolynomial

variable {σ τ υ R : Type*} [CommSemiring R] {f : σ → τ} (hf : Function.Injective f)

lemma killCompl_surjective : Function.Surjective (killCompl (R := R) hf) := by
  apply Function.HasRightInverse.surjective
  use rename f
  intro p
  exact killCompl_rename_app hf p

open Classical in
lemma rename_comp_killCompl :
    (rename (R := R) f).comp (killCompl hf) =
    MvPolynomial.aeval (fun i ↦ if i ∈ Set.range f then MvPolynomial.X i else 0) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [killCompl]
  simp only [aeval_eq_bind₁, AlgHom.coe_comp, Function.comp_apply, bind₁_X_right]
  by_cases h : i ∈ Set.range f
  · simp only [h, ↓reduceDIte, rename_X, ↓reduceIte]
    congr
    have :f ((Equiv.ofInjective f hf).symm ⟨i, h⟩) = (f ∘ (Equiv.ofInjective f hf).symm) ⟨i, h⟩ :=by
      simp only [Function.comp_apply]
    rw [this, Equiv.self_comp_ofInjective_symm]
  · simp only [h, ↓reduceDIte, map_zero, ↓reduceIte]

open Classical in
lemma rename_comp_killCompl_apply (p : MvPolynomial τ R) :
    (rename (R := R) f) ((killCompl hf) p) =
    (MvPolynomial.aeval (fun i ↦ if i ∈ Set.range f then MvPolynomial.X i else 0)) p :=
  congrFun (congrArg DFunLike.coe (rename_comp_killCompl hf)) p

open Classical in
lemma ker_killCompl_eq_ker_aeval : RingHom.ker (MvPolynomial.killCompl (R := R) hf) =
    RingHom.ker (MvPolynomial.aeval (S₁ := MvPolynomial τ R)
    (fun i ↦ if i ∈ Set.range f then MvPolynomial.X i else 0)) := by
  ext p
  rw [RingHom.mem_ker, RingHom.mem_ker, ← rename_comp_killCompl_apply hf]
  exact Iff.symm (map_eq_zero_iff (rename f) (rename_injective f hf))

end

section

lemma MvPolynomial.linearMap_eq_linearMap {R σ : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] {f g : MvPolynomial σ R →ₗ[R] M}
    (h : ∀ (s : σ →₀ ℕ), f ∘ₗ monomial s = g ∘ₗ monomial s) (p : MvPolynomial σ R) :
    f p = g p := LinearMap.congr_fun (MvPolynomial.linearMap_ext h) p

end

section

variable (R : Type*) (ι : Type*) [Infinite ι] (n : ℕ)

noncomputable def qiucbc : (Fin n) → ι := fun i ↦ Infinite.natEmbedding ι i.val

lemma uiqg : (qiucbc ι n).Injective :=
  Function.Injective.comp (Infinite.natEmbedding ι).injective Fin.val_injective

lemma qiubdwq [CommRing R] [IsNoetherianRing R] [Nontrivial R] :
    Function.Surjective (MvPolynomial.killCompl (R := R) <| uiqg ι n) := by
  apply Function.HasRightInverse.surjective
  use MvPolynomial.rename (qiucbc ι n)
  intro p
  exact MvPolynomial.killCompl_rename_app (uiqg ι n) p

noncomputable def w2ohd [CommRing R] [IsNoetherianRing R] [Nontrivial R] :=
  RingHom.ker (MvPolynomial.killCompl (R := R) <| uiqg ι n)

#check MvPolynomial.linearMap_ext
#check MvPolynomial.monomial


lemma qwugqw' [CommRing R] [IsNoetherianRing R] [Nontrivial R] :
    w2ohd R ι (n + 1) < w2ohd R ι n := by
  classical
  repeat rw [w2ohd, ker_killCompl_eq_ker_aeval]
  constructor
  · intro p hp
    rw [SetLike.mem_coe, RingHom.mem_ker] at *
    apply MvPolynomial.aeval_eq_zero
    intro d hne

    sorry
  · sorry

noncomputable def qoif [CommRing R] [IsNoetherianRing R] [Nontrivial R] :=
  RingHom.quotientKerEquivOfSurjective (qiubdwq R ι n)

lemma qilugf' [Field R] : (w2ohd R ι n).IsPrime := by
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact Equiv.isDomain <| qoif R ι n

noncomputable def qowinc [Field R] : LTSeries (PrimeSpectrum (MvPolynomial ι R)) where
  length := n
  toFun i := ⟨w2ohd R ι (n - i), qilugf' R ι (n - i)⟩
  step i := by
    dsimp only [Fin.coe_castSucc, Fin.val_succ]
    have : n - i - 1 + 1 = n - i := Nat.sub_add_cancel <| Nat.le_sub_of_add_le' i.prop
    exact this ▸ qwugqw' R ι (n - i - 1)

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
  · letI : Field R := hisfield.toField
    rw [ringKrullDim, Order.krullDim_eq_top_iff]
    constructor
    intro n
    use qowinc R ι n
    rfl

end
