import Mathlib
import Polydim.Dimension.Homomorphism
import Polydim.GoingDown.GoingDown

variable {A : Type*} [CommRing A]

open Polynomial

-- for some reason this is missing in mathlib, but we have the existence of a basis
instance : Module.Free A A[X] := Module.Free.of_basis <| Polynomial.basisMonomials A

/-- `(A ⧸ I)[X]` is isomorphic to `A[X] / I`. -/
noncomputable def polynomialQuotient (I : Ideal A) :
    (A[X] ⧸ (I.map <| algebraMap A A[X])) ≃ₐ[A] (A ⧸ I)[X] :=
  AlgEquiv.ofRingEquiv (f := (Ideal.polynomialQuotientEquivQuotientPolynomial I).symm)
  (by
    intro x
    dsimp only [algebraMap_eq, Polynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq]
    have : algebraMap A (A[X] ⧸ Ideal.map C I) =
        (algebraMap A[X] (A[X] ⧸ Ideal.map C I)).comp (algebraMap A A[X]) := by
      rfl
    rw [this]
    rw [Ideal.Quotient.algebraMap_eq, algebraMap_eq, RingHom.coe_comp, Function.comp_apply,
      Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk, map_C]
  )

section

lemma Ideal.map_isMaximal_of_surjective {R S F : Type*} [Ring R] [Ring S] [FunLike F R S]
    [rc : RingHomClass F R S] {f : F}
    (hf : Function.Surjective ⇑f) {I : Ideal R} [H : I.IsMaximal]
    (hk : RingHom.ker f ≤ I) : (Ideal.map f I).IsMaximal := by
  have := Ideal.map_eq_top_or_isMaximal_of_surjective f hf H
  rw [or_iff_not_imp_left] at this
  apply this
  by_contra h
  replace h := congr_arg (comap f) h
  rw [comap_map_of_surjective _ hf, comap_top] at h
  have := eq_top_iff.mpr <| h ▸ sup_le (le_of_eq rfl) hk
  exact H.ne_top this

end

section

lemma Ismaximal.height_eq_one {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {m : Ideal R} [hm : m.IsMaximal] :
  m.primeHeight = 1 := sorry

lemma ringKrullDim_eq_one {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    ringKrullDim R = 1 := sorry

end

/-- Let `p` be a prime ideal of `A`. If `P` is a prime ideal of `A[X]` maximal
among the prime ideals lying over `p`, `ht(P) = ht(p) + 1`. -/
lemma Ideal.primeHeight_polynomial_of_isMaximal [IsNoetherianRing A] (p : Ideal A)
    [p.IsMaximal] (P : Ideal A[X]) [P.IsMaximal] [P.LiesOver p] :
    P.primeHeight = p.primeHeight + 1 := by
  letI : Field (A ⧸ p) := Quotient.field p
  have : (P.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A[X]) p))).primeHeight = 1 := by
    let e : (A[X] ⧸ (Ideal.map C p)) ≃+* (A ⧸ p)[X] :=
      (Ideal.polynomialQuotientEquivQuotientPolynomial p).symm
    let P' : Ideal (A ⧸ p)[X] :=
      Ideal.map e <| Ideal.map (Ideal.Quotient.mk <| Ideal.map (algebraMap A A[X]) p) P
    -- use that `P'` is a maximal ideal of `(A ⧸ p)[X]`
    have : (P.map (Ideal.Quotient.mk <| map (algebraMap A A[X]) p)).IsMaximal := by
      apply Ideal.map_isMaximal_of_surjective
      · exact Quotient.mk_surjective
      rw [mk_ker]
      have : Ideal.comap (algebraMap A A[X]) P = p := by
        exact Eq.symm LiesOver.over
      rw [← this]
      exact map_comap_le
    letI : P'.IsMaximal := map_isMaximal_of_equiv e
    have : P'.primeHeight = 1 := Ismaximal.height_eq_one
    simp only [P'] at this
    rwa [← height_eq_of_ringEquiv e <|
      P.map (Ideal.Quotient.mk <| p.map (algebraMap A A[X]))]

  rw [primeHeight_eq_primeHeight_add_of_liesOver_of_flat p, this]

lemma IsLocalization.IsMaximal_of_IsMaximal_disjoint {R : Type*} [CommSemiring R] (M : Submonoid R)
    (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization M S] (J : Ideal S)
    (h : (Ideal.comap (algebraMap R S) J).IsMaximal) (disj : Disjoint (M : Set R) (Ideal.comap (algebraMap R S) J)) :
    J.IsMaximal := by
  obtain ⟨m, maxm, hm⟩ := Ideal.exists_le_maximal J <| Ideal.IsPrime.ne_top <|
    (IsLocalization.isPrime_iff_isPrime_disjoint M S J).mpr ⟨h.isPrime, disj⟩
  have : (Ideal.comap (algebraMap R S) J) ≤ (Ideal.comap (algebraMap R S) m) := fun x h ↦ by
    rw [Ideal.mem_comap] at h ⊢
    exact (hm h)
  have := Ideal.IsMaximal.eq_of_le h (Ideal.IsPrime.ne_top <| Ideal.IsPrime.under R m) this
  have : J = m := by rw [← IsLocalization.map_comap M S J, ← IsLocalization.map_comap M S m, this]
  exact this ▸ maxm

section

variable (S : Submonoid A) (Aₚ : Type*) [CommRing Aₚ] [Algebra A Aₚ] [IsLocalization S Aₚ]

noncomputable instance : Algebra A[X] Aₚ[X] :=
  RingHom.toAlgebra (Polynomial.mapRingHom (algebraMap A Aₚ))

noncomputable instance : IsScalarTower A A[X] Aₚ[X] := IsScalarTower.of_algebraMap_eq <| by
  have : algebraMap A[X] Aₚ[X] = Polynomial.mapRingHom (algebraMap A Aₚ) := by rfl
  rw [this]
  intro a
  simp only [Polynomial.algebraMap_apply, algebraMap_eq, coe_mapRingHom, map_C]

noncomputable instance : IsLocalization (Submonoid.map (algebraMap A A[X]) <| S) Aₚ[X] := by
  rw [Polynomial.algebraMap_eq]
  -- #check Polynomial.isLocalization
  sorry

end

/-- Let `p` be a prime ideal of `A`. If `P` is a prime ideal of `A[X]` maximal
among the prime ideals lying over `p`, `ht(P) = ht(p) + 1`. -/
lemma Ideal.primeHeight_polynomial [IsNoetherianRing A] (p : Ideal A)
    [hp : p.IsPrime] (P : Ideal A[X]) [hP : P.IsMaximal] [plo : P.LiesOver p] :
    P.primeHeight = p.primeHeight + 1 := by
  let Aₚ := Localization.AtPrime p
  have disj : Disjoint (Submonoid.map (algebraMap A A[X]) p.primeCompl : Set A[X]) P := by
    apply Set.disjoint_left.mpr
    intro a ha1 ha2
    simp only [algebraMap_eq, Submonoid.coe_map, Set.mem_image, SetLike.mem_coe] at ha1
    obtain ⟨b, hb⟩ := ha1
    have : b ∈ p := by
      rw [plo.over, mem_comap, algebraMap_eq]
      exact hb.2 ▸ ha2
    exact hb.1 this
  have eq : (comap (algebraMap A[X] Aₚ[X]) (map (algebraMap A[X] Aₚ[X]) P)) = P :=
      IsLocalization.comap_map_of_isPrime_disjoint _ _ P hP.isPrime disj
  set p' := p.map (algebraMap A Aₚ)
  letI : p'.IsMaximal := by
    have : p' = IsLocalRing.maximalIdeal Aₚ := Localization.AtPrime.map_eq_maximalIdeal
    exact this ▸ IsLocalRing.maximalIdeal.isMaximal Aₚ
  have eq1 : p.primeHeight = p'.primeHeight := by
    rw [IsLocalization.height_eq_of_disjoint p.primeCompl]
    exact Disjoint.symm <| Set.disjoint_left.mpr fun _ a b ↦ b a
  set P' : Ideal Aₚ[X] := P.map (algebraMap A[X] Aₚ[X])
  have mp : P'.IsMaximal :=
    IsLocalization.IsMaximal_of_IsMaximal_disjoint _ _ _ (eq.symm ▸ hP) (eq.symm ▸ disj)
  have lo : P'.LiesOver p' := by
    constructor
    have h1 : p'.under A = p := IsLocalization.comap_map_of_isPrime_disjoint p.primeCompl
        _ p hp <| Disjoint.symm <| Set.disjoint_left.mpr fun _ a b ↦ b a
    have h2 : P'.under A[X] = P := IsLocalization.comap_map_of_isPrime_disjoint
      (Submonoid.map (algebraMap A A[X]) <| p.primeCompl) Aₚ[X] P hP.isPrime disj
    have := plo.over
    rw [← h2, Ideal.under_under, ← Ideal.under_under P' (B := Aₚ)] at this
    simp only [p', this]
    nth_rw 1 [Ideal.under_def]
    exact IsLocalization.map_comap p.primeCompl Aₚ (P'.under Aₚ)
  have eq2 : P.primeHeight = P'.primeHeight := by
    rw [IsLocalization.height_eq_of_disjoint (Submonoid.map (algebraMap A A[X]) <| p.primeCompl) _ disj]
  rw [eq1, eq2]
  apply Ideal.primeHeight_polynomial_of_isMaximal p' P'

lemma Ideal.exists_ideal_liesOver_polynomial_of_isPrime [Nontrivial A] (p : Ideal A)
    [p.IsPrime] : ∃ (P : Ideal A[X]), P.IsPrime ∧ P.LiesOver p := by
  letI := Module.FaithfullyFlat.instOfNontrivialOfFree A A[X]
  obtain ⟨P, hP⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (B := A[X]) ⟨p, by assumption⟩
  exact ⟨P.asIdeal, ⟨PrimeSpectrum.isPrime P, ⟨by rw [Ideal.under_def, ← PrimeSpectrum.comap_asIdeal, hP]⟩⟩⟩

lemma le_ringKrullDim_polynomial [IsNoetherianRing A] :
    ringKrullDim A + 1 ≤ ringKrullDim A[X] := by
  nontriviality A
  by_cases h : FiniteDimensionalOrder (PrimeSpectrum A)
  obtain ⟨p, _, hp⟩ := Ideal.exists_isMaximal_height_eq_of_nontrivial (A := A)
  obtain ⟨P, _, hP⟩ := p.exists_ideal_liesOver_polynomial_of_isPrime
  obtain ⟨Q, mQ, hPQ⟩ := P.exists_le_maximal <| Ideal.IsPrime.ne_top <| by simpa
  have : Q.LiesOver p := ⟨Ideal.IsMaximal.eq_of_le (by assumption) Ideal.IsPrime.ne_top'
    (hP.over ▸ fun x a ↦ hPQ a)⟩
  have : Q.primeHeight = p.primeHeight + 1 :=
    p.primeHeight_polynomial Q
  rw [← hp, ← WithBot.coe_one, ← WithBot.coe_add, ← this]
  exact (ringKrullDim_le_of_height_le (ringKrullDim A[X]) (A := A[X])).mp (by rfl) Q mQ.isPrime
  have : ringKrullDim A[X] = ⊤ := by sorry
  rw [this]
  exact OrderTop.le_top _

lemma ringKrullDim_polynomial_le [IsNoetherianRing A] :
    ringKrullDim A[X] ≤ ringKrullDim A + 1 := by
  nontriviality A[X]
  have : Nontrivial A := Polynomial.nontrivial_iff.mp (by assumption)
  by_cases h : FiniteDimensionalOrder (PrimeSpectrum A[X])
  obtain ⟨P, _, hP⟩ := Ideal.exists_isMaximal_height_eq_of_nontrivial (A := A[X])
  let p : Ideal A := P.comap (algebraMap A A[X])
  rw [← hP, Ideal.primeHeight_polynomial p P, WithBot.coe_add, WithBot.coe_one]
  have := (ringKrullDim_le_of_height_le (ringKrullDim A) (A := A)).mp (by rfl) p (Ideal.IsPrime.under A P)
  exact add_le_add_right this 1
  have : ringKrullDim A = ⊤ := by sorry
  rw [this]
  exact StrictMono.maximal_preimage_top (fun _ _ a ↦ a) rfl _

/-- `dim A[X] = dim A + 1` if `A` is Noetherian. -/
theorem ringKrullDim_polynomial [IsNoetherianRing A] :
    ringKrullDim A[X] = ringKrullDim A + 1 := by
  apply le_antisymm
  exact ringKrullDim_polynomial_le
  exact le_ringKrullDim_polynomial
