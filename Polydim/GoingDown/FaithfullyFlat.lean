import Mathlib

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
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
  have : Function.Injective (rTensor B τ) := by
    set g := TensorProduct.assoc A B M B
    have : (rTensor B τ) = g.symm.comp (TensorProduct.mk A B (M ⊗[A] B) 1) := by
      unfold rTensor τ g
      apply TensorProduct.ext'
      intro x y
      simp only [map_tmul, mk_apply, id_coe, id_eq, coe_comp, LinearEquiv.coe_coe,
        Function.comp_apply, assoc_symm_tmul]
    rw [this]
    simp only [coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective]
    letI : Module B (M ⊗[A] B) := by

      sorry
    letI : IsScalarTower A B (M ⊗[A] B) := by

      sorry
    exact Module.tensorProduct_mk_injective_of_isScalarTower (M ⊗[A] B)
  have h1 := ker_eq_bot.mpr this ▸ (Module.Flat.rTensor_exact B <| exact_subtype_ker_map τ).linearMap_ker_eq
  have h2 : Function.Injective (rTensor B (ker τ).subtype) := by
    have h3 := (Module.Flat.rTensor_exact B <| exact_subtype_ker_map (ker τ).subtype).linearMap_ker_eq
    have : (ker (ker τ).subtype).subtype = 0 :=
      (Submodule.ker_subtype (ker τ)) ▸ (Subsingleton.eq_zero _)
    simp only [this, rTensor_zero, range_zero] at h3
    exact ker_eq_bot.mp h3
  have : Subsingleton (ker τ ⊗[A] B) := by
    apply subsingleton_iff.mpr
    intro x y
    have h : ∀ a : (ker τ) ⊗[A] B, (rTensor B (ker τ).subtype) a = 0 :=
      fun a ↦ (Submodule.mem_bot _).mp (h1.symm ▸ mem_range_self (rTensor B (ker τ).subtype) a)
    exact h2 (by rw [h x, h y])
  exact Submodule.subsingleton_iff_eq_bot.mp (rTensor_reflects_triviality A B (ker τ))

-- Bonus
/-- If `M →ₗ[A] B ⊗[A] M` is injective for every `A`-module `M`, `B` is a faithfully flat
`A`-algebra. -/
lemma Module.FaithfullyFlat.of_tensorProduct_mk_injective
    (h : ∀ (M : Type*) [AddCommGroup M] [Module A M], Function.Injective (TensorProduct.mk A B M)) :
    FaithfullyFlat A B :=
  -- easy, use `Module.FaithfullyFlat.iff_flat_and_lTensor_faithful`
  sorry

/-- If `B` is a faithfully flat `A`-algebra, the preimage of the pushforward of any
ideal `I` is again `I`. -/
lemma Ideal.comap_map_eq_self_of_faithfullyFlat [Module.FaithfullyFlat A B] (I : Ideal A) :
    (I.map (algebraMap A B)).comap (algebraMap A B) = I := by
  apply le_antisymm
  · -- use `Module.FaithfullyFlat.tensorProduct_mk_injective` for `M = A ⧸ I`
    -- and consider the map `A / I →+* (A / I) ⊗[A] B ≃+* B ⧸ (I.map <| algebraMap A B)`
    sorry
  · exact le_comap_map

/-- If `B` is a faithfully-flat `A`-algebra, every ideal in `A` is the preimage of some ideal
in `B`. -/
lemma Ideal.comap_surjective_of_faithfullyFlat [Module.FaithfullyFlat A B] :
    Function.Surjective (Ideal.comap (algebraMap A B)) :=
  fun I ↦ ⟨I.map (algebraMap A B), comap_map_eq_self_of_faithfullyFlat I⟩

/-- If `B` is a faithfully flat `A`-algebra, the induced map on the prime spectrum is
surjective. -/
lemma PrimeSpectrum.comap_surjective_of_faithfullyFlat [Module.FaithfullyFlat A B] :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) := by
  intro I
  have : (I.asIdeal.map (algebraMap A B)).IsPrime := by sorry
  -- easy from `Ideal.comap_surjective_of_faithfullyFlat`
  sorry

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
