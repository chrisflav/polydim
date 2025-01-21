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
  {g : τ → υ} (hg : Function.Injective g)

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
    rw [Equiv.apply_ofInjective_symm hf]
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

lemma killCompl_killCompl : (killCompl (R := R) hf).comp (killCompl hg) =
    (killCompl (Function.Injective.comp hg hf)) := by
  apply MvPolynomial.algHom_ext
  intro i
  unfold killCompl
  by_cases hrange : i ∈ Set.range (g ∘ f)
  · have hrangeg : i ∈ Set.range g := by
      rw [Set.range_comp] at hrange
      exact Set.mem_range_of_mem_image g (Set.range f) hrange
    have hrangef : (Equiv.ofInjective g hg).symm ⟨i, hrangeg⟩ ∈ Set.range f := by
      rw [Set.range_comp] at hrange
      apply Set.mem_image_equiv.mp
      rcases hrange with ⟨j, hjmem, hjmap⟩
      use j
      constructor
      · exact hjmem
      rw [Equiv.ofInjective_apply, Subtype.mk.injEq]
      exact hjmap
    simp only [Set.mem_range, aeval_eq_bind₁, AlgHom.coe_comp, Function.comp_apply, bind₁_X_right,
      hrangeg, ↓reduceDIte, hrangef, hrange]
    congr
    have : g (f ((Equiv.ofInjective f hf).symm ⟨(Equiv.ofInjective g hg).symm ⟨i, hrangeg⟩, hrangef⟩)) =
        (g ∘ f) ((Equiv.ofInjective (g ∘ f) (Function.Injective.comp hg hf)).symm ⟨i, hrange⟩) := by
      rw [Equiv.apply_ofInjective_symm hf, Equiv.apply_ofInjective_symm hg,
        Equiv.apply_ofInjective_symm (Function.Injective.comp hg hf)]
    rw [Function.comp_apply] at this
    exact hf (hg this)
  · by_cases hrangeg : i ∈ Set.range g
    · have hrangef : (Equiv.ofInjective g hg).symm ⟨i, hrangeg⟩ ∉ Set.range f := by
        contrapose! hrange
        rcases hrangeg with ⟨j, hjmap⟩
        rcases hrange with ⟨k, hkmap⟩
        use k
        rw [Function.comp_apply, hkmap, Equiv.apply_ofInjective_symm hg]
      simp only [Set.mem_range, aeval_eq_bind₁, AlgHom.coe_comp, Function.comp_apply, bind₁_X_right,
        hrangeg, ↓reduceDIte, hrangef, hrange]
    · simp only [Set.mem_range, aeval_eq_bind₁, AlgHom.coe_comp, Function.comp_apply,
      bind₁_X_right, hrangeg, ↓reduceDIte, map_zero, hrange]

end

section

variable (R : Type*) (ι : Type*) [Infinite ι] (n : ℕ)

noncomputable def Infinite.finEmbedding : (Fin n) ↪ ι where
  toFun i := Infinite.natEmbedding ι i.val
  inj' := Function.Injective.comp (Infinite.natEmbedding ι).injective Fin.val_injective

def oqin : Fin n → Fin (n + 1) := by
  exact fun a ↦ Fin.castAdd 1 a


lemma Infinite.finEmbedding_castAdd (m : ℕ) : Infinite.finEmbedding ι n =
    (Infinite.finEmbedding ι (n + m)) ∘ (Fin.castAdd m) := by
  ext x
  unfold Infinite.finEmbedding
  dsimp only [Function.Embedding.coeFn_mk, Function.comp_apply, Fin.coe_castAdd]

lemma Infinite.finEmbedding_val : Infinite.finEmbedding ι n =
    (Infinite.natEmbedding ι) ∘ (Fin.val (n := n)) := by
  ext x
  unfold Infinite.finEmbedding
  rw [Function.Embedding.coeFn_mk, Function.comp_apply]

lemma MvPolynomial.killCompl_FincastAdd_comp_killCompl_finEmbedding_aux
    (m : ℕ) [CommRing R] [IsNoetherianRing R] [Nontrivial R] :
    (MvPolynomial.killCompl (R := R) (Fin.castAdd_injective n m)).comp
    (MvPolynomial.killCompl (Infinite.finEmbedding ι (n + m)).injective) =
    (MvPolynomial.killCompl (R := R) (Infinite.finEmbedding ι n).injective) := by
  rw [killCompl_killCompl]

-- The ideal we want is (X i, when i is not 1 ... n)
noncomputable def MvPolynomial.ker_killCompl_finEmbedding_aux
    [CommRing R] [IsNoetherianRing R] [Nontrivial R] :=
  RingHom.ker (MvPolynomial.killCompl (R := R) <| (Infinite.finEmbedding ι n).injective)

lemma MvPolynomial.ker_killCompl_finEmbedding_le_aux
    [CommRing R] [IsNoetherianRing R] [Nontrivial R] :
    MvPolynomial.ker_killCompl_finEmbedding_aux R ι (n + 1) <
    MvPolynomial.ker_killCompl_finEmbedding_aux R ι n := by
  unfold MvPolynomial.ker_killCompl_finEmbedding_aux
  constructor
  · intro p hp
    rw [SetLike.mem_coe, RingHom.mem_ker] at hp ⊢
    rw [← MvPolynomial.killCompl_FincastAdd_comp_killCompl_finEmbedding_aux _ _ _ 1,
      AlgHom.coe_comp, Function.comp_apply, hp, map_zero]
  · rw [Set.not_subset]
    use MvPolynomial.X  ((Infinite.natEmbedding ι) n)
    unfold MvPolynomial.killCompl
    constructor
    · simp only [Set.mem_range, MvPolynomial.aeval_eq_bind₁, SetLike.mem_coe, RingHom.mem_ker,
        MvPolynomial.bind₁_X_right, dite_eq_right_iff, MvPolynomial.X_ne_zero, imp_false,
        not_exists]
      intro x
      by_contra h
      rw [Infinite.finEmbedding_val, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq] at h
      have := x.prop
      linarith
    · simp only [Set.mem_range, MvPolynomial.aeval_eq_bind₁, SetLike.mem_coe, RingHom.mem_ker,
        MvPolynomial.bind₁_X_right, dite_eq_right_iff, MvPolynomial.X_ne_zero, imp_false,
        not_exists, not_forall, not_not]
      use ⟨n, lt_add_one n⟩
      unfold Infinite.finEmbedding
      dsimp only [Function.Embedding.coeFn_mk]

lemma MvPolynomial.ker_killCompl_finEmbedding_isPrime_aux [Field R] :
    (MvPolynomial.ker_killCompl_finEmbedding_aux R ι n).IsPrime := by
  rw [← Ideal.Quotient.isDomain_iff_prime]
  letI e := RingHom.quotientKerEquivOfSurjective
    (killCompl_surjective (R := R) <| (Infinite.finEmbedding ι n).injective)
  exact Equiv.isDomain <| e

noncomputable def MvPolynomial.infinite_LTSeries_aux [Field R] : LTSeries (PrimeSpectrum (MvPolynomial ι R)) where
  length := n
  toFun i := ⟨MvPolynomial.ker_killCompl_finEmbedding_aux R ι (n - i),
    MvPolynomial.ker_killCompl_finEmbedding_isPrime_aux R ι (n - i)⟩
  step i := by
    dsimp only [Fin.coe_castSucc, Fin.val_succ]
    have : n - i - 1 + 1 = n - i := Nat.sub_add_cancel <| Nat.le_sub_of_add_le' i.prop
    exact this ▸ MvPolynomial.ker_killCompl_finEmbedding_le_aux R ι (n - i - 1)

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
    use MvPolynomial.infinite_LTSeries_aux R ι n
    rfl

end
