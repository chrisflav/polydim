import Mathlib
import Polydim.GoingDown.PrimeSpectrum

universe u v

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [Module.Flat A B]

open TensorProduct LinearMap

omit [Module.Flat A B] in
lemma Module.tensorProduct_mk_injective_of_isScalarTower (M : Type*) [AddCommGroup M] [Module A M]
    [Module B M] [IsScalarTower A B M] :
    Function.Injective (TensorProduct.mk A B M 1) := by
  set f := TensorProduct.mk A B M 1
  set g : B ⊗[A] M →ₗ[B] M := LinearMap.liftBaseChange B LinearMap.id
  have h : Function.RightInverse f g := by
    intro m
    unfold f g
    simp only [mk_apply, LinearMap.liftBaseChange_tmul, LinearMap.id_coe, id_eq, one_smul]
  exact Function.RightInverse.injective h

/-- If `B` is a faithfully flat `A`-module and `M` is any `A`-module, the canonical
map `M →ₗ[A] B ⊗[A] M` is injective. -/
lemma Module.FaithfullyFlat.tensorProduct_mk_injective [Module.FaithfullyFlat A B]
      (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Injective (TensorProduct.mk A B M 1) := by
  set τ := TensorProduct.mk A B M 1
  apply ker_eq_bot.mp
  have : Function.Injective (lTensor B τ) := by
    set g := TensorProduct.leftComm A B B M
    have : (lTensor B τ) = g.symm.comp (TensorProduct.mk A B (B ⊗[A] M) 1) := by
      unfold lTensor τ g
      apply TensorProduct.ext'
      intro x y
      simp only [map_tmul, id_coe, id_eq, mk_apply, coe_comp, LinearEquiv.coe_coe,
        Function.comp_apply, leftComm_symm_tmul]
    rw [this, coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective]
    exact Module.tensorProduct_mk_injective_of_isScalarTower _
  have h1 := ker_eq_bot.mpr this ▸ (Module.Flat.lTensor_exact B <| exact_subtype_ker_map τ).linearMap_ker_eq
  have h2 : Function.Injective (lTensor B (ker τ).subtype) := by
    have h3 := (Module.Flat.lTensor_exact B <| exact_subtype_ker_map (ker τ).subtype).linearMap_ker_eq
    have : (ker (ker τ).subtype).subtype = 0 :=
      (Submodule.ker_subtype (ker τ)) ▸ (Subsingleton.eq_zero _)
    rw [this, lTensor_zero, range_zero] at h3
    exact ker_eq_bot.mp h3
  have : Subsingleton (B ⊗[A] ker τ) := by
    apply subsingleton_iff.mpr
    intro x y
    have h : ∀ a : B ⊗[A] (ker τ), (lTensor B (ker τ).subtype) a = 0 :=
      fun a ↦ (Submodule.mem_bot _).mp (h1.symm ▸ mem_range_self (lTensor B (ker τ).subtype) a)
    exact h2 (by rw [h x, h y])
  exact Submodule.subsingleton_iff_eq_bot.mp (lTensor_reflects_triviality A B (ker τ))

-- Bonus
/-- If `M →ₗ[A] B ⊗[A] M` is injective for every `A`-module `M`, `B` is a faithfully flat
`A`-algebra. -/
lemma Module.FaithfullyFlat.of_tensorProduct_mk_injective
    (h : ∀ (M : Type (max u v)) [AddCommGroup M] [Module A M], Function.Injective (TensorProduct.mk A B M 1)) :
    FaithfullyFlat A B := by
  rw [Module.FaithfullyFlat.iff_flat_and_lTensor_faithful]
  constructor
  · assumption
  · intro N _ _ hN
    haveI : Nontrivial N := hN
    exact Function.Injective.nontrivial <| h N
  -- easy, use `Module.FaithfullyFlat.iff_flat_and_lTensor_faithful`

section
variable (B : Type v) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)

noncomputable def TensorProduct.tensorQuotEquivQuotIdealMap' (I : Ideal A) :
    TensorProduct A B (A ⧸ I) ≃ₗ[A] B ⧸ (I.map <| algebraMap A B) :=
  (TensorProduct.tensorQuotEquivQuotSMul B I)
  ≪≫ₗ (Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map I))
  ≪≫ₗ (Submodule.Quotient.restrictScalarsEquiv A (I.map <| algebraMap A B))

@[simp]
lemma TensorProduct.tensorQuotEquivQuotIdealMap'_apply (b : B) (a : A) :
    TensorProduct.tensorQuotEquivQuotIdealMap' B I (b ⊗ₜ[A] (Ideal.Quotient.mk I) a) =
    Submodule.Quotient.mk (a • b) :=
  rfl

@[simp]
lemma TensorProduct.tensorQuotEquivQuotIdealMap'_symm_mk (b : B) :
    (TensorProduct.tensorQuotEquivQuotIdealMap' B I).symm
    (Ideal.Quotient.mk (I.map <| algebraMap A B) b) = b ⊗ₜ[A] 1 :=
  rfl

noncomputable def TensorProduct.tensorQuotEquivQuotIdealMap'' (I : Ideal A) :
    (B ⧸ (I.map <| algebraMap A B)) ≃ₐ[A] TensorProduct A B (A ⧸ I) :=
  AlgEquiv.ofLinearEquiv (TensorProduct.tensorQuotEquivQuotIdealMap' B I).symm
  (by
    have := TensorProduct.tensorQuotEquivQuotIdealMap'_symm_mk B I 1
    simpa only [map_one]
  )
  (by
    intro x y
    induction' x using Submodule.Quotient.induction_on with u
    induction' y using Submodule.Quotient.induction_on with v
    simp only [Ideal.Quotient.mk_eq_mk, ← map_mul,
      TensorProduct.tensorQuotEquivQuotIdealMap'_symm_mk, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one]
  )

noncomputable def TensorProduct.tensorQuotEquivQuotIdealMap (I : Ideal A) :
    TensorProduct A B (A ⧸ I) ≃ₐ[A] B ⧸ (I.map <| algebraMap A B) :=
  (TensorProduct.tensorQuotEquivQuotIdealMap'' B I).symm

@[simp]
lemma TensorProduct.tensorQuotEquivQuotIdealMap_apply (b : B) (a : A) :
    TensorProduct.tensorQuotEquivQuotIdealMap B I (b ⊗ₜ[A] (Ideal.Quotient.mk I) a) =
    Submodule.Quotient.mk (a • b) :=
  rfl

@[simp]
lemma TensorProduct.tensorQuotEquivQuotIdealMap_symm_mk (b : B) :
    (TensorProduct.tensorQuotEquivQuotIdealMap B I).symm
    (Ideal.Quotient.mk (I.map <| algebraMap A B) b) = b ⊗ₜ[A] 1 :=
  rfl

end

/-- If `B` is a faithfully flat `A`-algebra, the preimage of the pushforward of any
ideal `I` is again `I`. -/
lemma Ideal.comap_map_eq_self_of_faithfullyFlat [Module.FaithfullyFlat A B] (I : Ideal A) :
    (I.map (algebraMap A B)).comap (algebraMap A B) = I := by
  apply le_antisymm
  · have inj : Function.Injective (AlgEquiv.toLinearMap (TensorProduct.tensorQuotEquivQuotIdealMap B I) ∘ₗ
        TensorProduct.mk A B (A ⧸ I) 1) := by
      rw [LinearMap.coe_comp]
      apply Function.Injective.comp
      · exact AlgEquiv.injective _
      · exact Module.FaithfullyFlat.tensorProduct_mk_injective (A ⧸ I)
    intro x hx
    rw [Ideal.mem_comap] at hx
    rw [← Ideal.Quotient.eq_zero_iff_mem] at *
    have : (AlgEquiv.toLinearMap (TensorProduct.tensorQuotEquivQuotIdealMap B I) ∘ₗ
        TensorProduct.mk A B (A ⧸ I) 1) x = 0 := by
      simp only [coe_comp, Function.comp_apply, mk_apply, AlgEquiv.toLinearMap_apply,
        tensorQuotEquivQuotIdealMap_apply, Quotient.mk_eq_mk]
      rw [← Algebra.algebraMap_eq_smul_one, hx]
    apply inj
    rw [this]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.mk_apply,
      TensorProduct.tmul_zero, map_zero]
  · exact le_comap_map

/-- If `B` is a faithfully-flat `A`-algebra, every ideal in `A` is the preimage of some ideal
in `B`. -/
lemma Ideal.comap_surjective_of_faithfullyFlat [Module.FaithfullyFlat A B] :
    Function.Surjective (Ideal.comap (algebraMap A B)) :=
  fun I ↦ ⟨I.map (algebraMap A B), comap_map_eq_self_of_faithfullyFlat I⟩

/-- If `B` is a faithfully flat `A`-algebra, the induced map on the prime spectrum is
surjective. -/
lemma PrimeSpectrum.comap_surjective_of_faithfullyFlat [Module.FaithfullyFlat A B] :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) := fun I ↦
  (PrimeSpectrum.mem_range_comap_iff (algebraMap A B) I).mpr
      I.asIdeal.comap_map_eq_self_of_faithfullyFlat

-- Bonus
/-- If `A →+* B` is flat and surjective on prime spectra, `B` is a faithfully flat `A`-algebra. -/
lemma Module.FaithfullyFlat.of_primeSpectrum_comap_surjective
    (h : Function.Surjective (PrimeSpectrum.comap (algebraMap A B))) :
    Module.FaithfullyFlat A B := by
  constructor
  intro m hm
  obtain ⟨m', hm'⟩ := h ⟨m, hm.isPrime⟩
  have : m = Ideal.comap (algebraMap A B) m'.asIdeal := by rw [← PrimeSpectrum.comap_asIdeal (algebraMap A B) m', hm']
  rw [Ideal.smul_top_eq_map, this]
  exact (Submodule.restrictScalars_eq_top_iff _ _ _).ne.mpr
    fun top ↦ m'.isPrime.ne_top <| top_le_iff.mp <| top ▸ Ideal.map_comap_le

/-- If `B` is a local, flat `A`-algebra and `A →+* B` is local, `B` is faithfully flat. -/
lemma Module.FaithfullyFlat.of_flat_of_isLocalHom [IsLocalRing A] [IsLocalRing B]
    [h : IsLocalHom (algebraMap A B)] : Module.FaithfullyFlat A B := by
  constructor
  intro m hm
  rw [Ideal.smul_top_eq_map, IsLocalRing.eq_maximalIdeal hm]
  by_contra eqt
  have : Submodule.restrictScalars A (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) ≤ Submodule.restrictScalars A (IsLocalRing.maximalIdeal B) := by
    exact ((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 0 2).mp h
  rw [eqt, top_le_iff, Submodule.restrictScalars_eq_top_iff] at this
  exact Ideal.IsPrime.ne_top' this
