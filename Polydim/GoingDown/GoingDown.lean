import Mathlib

import Polydim.GoingDown.FaithfullyFlat

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

noncomputable instance [Module.Flat A B] (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime]
    [P.LiesOver p] :
  Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
    (Localization.localRingHom p P (algebraMap A B) Ideal.LiesOver.over).toAlgebra

noncomputable instance [Module.Flat A B] (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime]
    [P.LiesOver p] :
  IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime P) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    have : (Localization.localRingHom p P (algebraMap A B) Ideal.LiesOver.over) = algebraMap (Localization.AtPrime p) (Localization.AtPrime P) := rfl
    rw [← this]
    simp only [RingHom.coe_comp, Function.comp_apply, Localization.localRingHom_to_map]
    exact rfl

instance [Module.Flat A B] (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    Module.Flat (Localization.AtPrime p) (Localization.AtPrime P) := by
  rw [Module.flat_iff_of_isLocalization (S := (Localization.AtPrime p)) (p := p.primeCompl)]
  exact Module.Flat.trans A B (Localization.AtPrime P)

/-- The going-down theorem for flat algebras. -/
lemma exists_isPrime_and_liesOver_of_isPrime_of_le_of_liesOver [Module.Flat A B] (p' p : Ideal A)
    [p'.IsPrime] [p.IsPrime]
    (hle : p' ≤ p) (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    ∃ (P' : Ideal B), P' ≤ P ∧ P'.IsPrime ∧ P'.LiesOver p' := by
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime P)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom p P (algebraMap A B) Ideal.LiesOver.over
  have : Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime P) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have disj : Disjoint (p.primeCompl : Set A) p' := by simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hle]
  let pl' : Ideal (Localization.AtPrime p) :=
    Ideal.map (algebraMap A _) p'
  have : ∃ (Pl' : Ideal (Localization.AtPrime P)), Pl'.IsPrime ∧ Pl'.LiesOver pl' := by
    have hp : pl'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl _ p' (by simpa) disj
    obtain ⟨Pl, hpl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (B := Localization.AtPrime P) ⟨pl', hp⟩
    exact ⟨Pl.asIdeal, ⟨PrimeSpectrum.isPrime Pl, ⟨by rw [Ideal.under_def, ← PrimeSpectrum.comap_asIdeal, hpl]⟩⟩⟩
  obtain ⟨Pl', hl, hlo⟩ := this
  refine ⟨Ideal.comap (algebraMap B _) Pl', ?_, ?_, ?_⟩
  · exact (IsLocalization.AtPrime.orderIsoOfPrime _ P ⟨Pl', hl⟩).2.2
  · exact Ideal.IsPrime.under B Pl'
  · unfold pl' at hlo
    replace hlo := hlo.over
    constructor
    rw [← Ideal.under_def, Ideal.under_under,
      ← Ideal.under_under (B := (Localization.AtPrime p)) Pl', ← hlo, Ideal.under_def,
      IsLocalization.comap_map_of_isPrime_disjoint _ _ p' (by simpa) disj]

section

def Algebra.HasGoingDown (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  ∀ (p q : Ideal R) [p.IsPrime] [q.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver q],
    p ≤ q → ∃ (P : Ideal S), P ≤ Q ∧ P.IsPrime ∧ P.LiesOver p

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

lemma Algebra.HasGoingDown.exists_ideal_liesOver_lt (h : Algebra.HasGoingDown R S) (p q : Ideal R)
    [p.IsPrime] [q.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver q] (hpq : p < q):
    ∃ (P : Ideal S), P < Q ∧ P.IsPrime ∧ P.LiesOver p := by
  obtain ⟨P, hPQ, _, _⟩ := h p q Q hpq.le
  have : P < Q := by
    by_contra hc
    have : P = Q := eq_of_le_of_not_lt hPQ hc
    subst this
    rw [Ideal.LiesOver.over (p := p) (P := P)] at hpq
    rw [Ideal.LiesOver.over (p := q) (P := P)] at hpq
    simp at hpq
  use P, this

lemma RelSeries.inductionOn {α : Type*} (r : Rel α α)
  (motive : RelSeries r → Prop)
  (h0 : (x : α) → motive (RelSeries.singleton r x))
  (hcons : (p : RelSeries r) → (x : α) → (hx : r x p.head) → (hp : motive p) → motive (p.cons x hx))
  (p : RelSeries r) :
  motive p := sorry

lemma Algebra.HasGoingDown.exists_ltSeries (h : Algebra.HasGoingDown R S)
    (l : LTSeries (PrimeSpectrum R)) (P : Ideal S) [P.IsPrime] [P.LiesOver l.last.asIdeal] :
    ∃ (L : LTSeries (PrimeSpectrum S)),
      L.length = l.length ∧
      L.last = ⟨P, inferInstance⟩ ∧
      ∀ i, (algebraMap R S).specComap (L i) = l i := by

  #check LTSeries.mk
  set L : LTSeries (PrimeSpectrum S) := {
    length := l.length
    toFun := Fin.reverseInduction ⟨P, inferInstance⟩ (λ i prev ↦ by
      #check h.exists_ideal_liesOver_lt
      sorry)
    step := sorry
  }
  sorry

end

lemma Algebra.HasGoingDown.of_flat [Module.Flat A B] : Algebra.HasGoingDown A B := by
  introv p _ Q _ _ hpq
  apply exists_isPrime_and_liesOver_of_isPrime_of_le_of_liesOver p q hpq Q


def descendingMap (n : ℕ) : Fin (n + 1) → ℕ :=
  Fin.reverseInduction
    (motive := λ _ ↦ ℕ) -- The return type is ℕ for all inputs
    (1) -- f n = 1 (base case)
    (λ i prev ↦ 2^prev) -- f k = 2^(f (k+1))

-- Let's test it with a small example
#eval descendingMap 2 ⟨0, by norm_num⟩ -- should give 2^(2^1)
#eval descendingMap 2 ⟨1, by norm_num⟩ -- should give 2^1
#eval descendingMap 2 ⟨2, by norm_num⟩ -- should give 1
