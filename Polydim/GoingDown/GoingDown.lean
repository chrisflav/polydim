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
  motive p := by sorry

lemma RelSeries.toList.get_eq_toFun {α : Type*} {r : Rel α α} (p : RelSeries r) (i : Fin (p.length + 1)) :
    p.toFun i = p.toList[i] := by
  simp only [Fin.getElem_fin, toList, List.getElem_ofFn p.toFun]

lemma RelSeries.toList.getElem_eq_toFun {α : Type*} {r : Rel α α} (p : RelSeries r) (i : ℕ) (h : i < p.length + 1) :
    p.toFun ⟨i, h⟩ = p.toList[i]'(length_toList p ▸ h) := by
  simp only [Fin.getElem_fin, toList, List.getElem_ofFn p.toFun]

lemma RelSeries.head_toList {α : Type*} {r : Rel α α} (p : RelSeries r) :
    p.head = p.toList[0] := by rw [head, toList.get_eq_toFun]; rfl

lemma RelSeries.append_toList {α : Type*} {r : Rel α α} (p q : RelSeries r) (rel : r p.last q.head) :
    (p.append q rel).toList = p.toList ++ q.toList := by
  apply List.ext_getElem (by
    simp only [toList, append_length, List.ofFn_succ, Fin.succ_zero_eq_one, List.length_cons,
      List.length_ofFn, List.append_eq, List.cons_append, List.length_append, add_left_inj]
    rfl)
  intro n h1 h2
  rw [← RelSeries.toList.getElem_eq_toFun _ _ (length_toList _ ▸ h1)]
  simp only [append_length, List.ofFn_succ, Fin.succ_zero_eq_one, List.length_cons,
    List.length_ofFn] at h1
  unfold append
  by_cases h : n < p.length + 1
  · simp only [List.getElem_append_left (length_toList p ▸ h), Function.comp_apply, Fin.cast_mk,
      Fin.append, Fin.addCases, dif_pos h, RelSeries.toList.getElem_eq_toFun p]
    rfl
  simp only [List.getElem_append_right (length_toList p ▸ not_lt.mp h), Function.comp_apply,
    Fin.cast_mk, Fin.append, Fin.addCases, dif_neg h, Fin.subNat_mk, Fin.natAdd_mk,
    eq_rec_constant, length_toList, RelSeries.toList.getElem_eq_toFun]

lemma RelSeries.cons_toList {α : Type*} {r : Rel α α} (p : RelSeries r) (a : α) (rel : r a p.head) :
    (p.cons a rel).toList = a :: p.toList := by rw [cons, append_toList]; rfl

lemma Algebra.HasGoingDown.exists_ltSeries (h : Algebra.HasGoingDown R S)
    (l : LTSeries (PrimeSpectrum R)) (P : Ideal S) [P.IsPrime] [lo : P.LiesOver l.last.asIdeal] :
    ∃ (L : LTSeries (PrimeSpectrum S)),
      L.length = l.length ∧
      L.last = ⟨P, inferInstance⟩ ∧
      List.map (algebraMap R S).specComap L.toList = l.toList := by
  induction' l using RelSeries.inductionOn with q l q lt ih generalizing P
  use RelSeries.singleton _ ⟨P, inferInstance⟩
  simp only [RelSeries.singleton_length, RelSeries.last_singleton, true_and]
  apply List.ext_get
  · simp only [List.length_map, RelSeries.length_toList, RelSeries.singleton_length, zero_add]
  intro n lt1 lt2
  simp only [List.length_map, RelSeries.length_toList, RelSeries.singleton_length, zero_add,
    Nat.lt_one_iff] at lt1 lt2
  simp only [List.get_eq_getElem, List.getElem_map, lt1]
  exact PrimeSpectrum.ext_iff.mpr lo.over.symm
  simp only [RelSeries.last_cons] at lo
  obtain ⟨L, len, last, spec⟩ := ih P
  letI : L.head.asIdeal.LiesOver l.head.asIdeal := by
    constructor
    rw [L.head_toList, l.head_toList, Ideal.under_def]
    have : (algebraMap R S).specComap L.toList[0] = l.toList[0] := by
      rw [List.getElem_map_rev (algebraMap R S).specComap]
      exact List.getElem_of_eq spec (i := 0) (by
        rw [List.length_map]
        exact (RelSeries.length_toList L) ▸ Nat.zero_lt_succ L.length)
    rw [RingHom.specComap, PrimeSpectrum.ext_iff] at this
    exact this.symm
  obtain ⟨Q, Qlt, hQ, Qlo⟩ := h.exists_ideal_liesOver_lt _ _ q.asIdeal l.head.asIdeal L.head.asIdeal lt
  use L.cons ⟨Q, hQ⟩ Qlt
  simp only [RelSeries.cons_length, add_left_inj, RelSeries.last_cons]
  exact ⟨len, last, by
  simp only [RelSeries.cons_toList, List.map_cons, spec, List.cons.injEq, and_true]
  exact PrimeSpectrum.ext_iff.mpr Qlo.over.symm⟩

end

lemma Algebra.HasGoingDown.of_flat [Module.Flat A B] : Algebra.HasGoingDown A B := by
  introv p _ Q _ _ hpq
  apply exists_isPrime_and_liesOver_of_isPrime_of_le_of_liesOver p q hpq Q
