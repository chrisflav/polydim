import Mathlib

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The height of a prime ideal in a ring is the supremum over the lengths of prime ideal
chains ending at `p`. -/
noncomputable def Ideal.primeHeight (p : Ideal A) : WithTop ℕ :=
  Set.chainHeight { q : Ideal A | q.IsPrime ∧ q < p }

lemma chainHeight_eq_orderHeight {α : Type*} [Preorder α] (p : α) :
    Set.chainHeight { q : α | q < p } = Order.height p := by
  sorry

lemma Ideal.primeHeight_eq_orderheight (p : Ideal A) [hp : p.IsPrime] :
    Ideal.primeHeight p = Order.height (⟨p, hp⟩ : PrimeSpectrum A) := by
  sorry

lemma Ideal.exists_series_of_primeHeight_ne_top (p : Ideal A) [p.IsPrime]
    (hp : p.primeHeight ≠ ⊤) :
    ∃ (l : LTSeries (PrimeSpectrum A)),
      RelSeries.last l = ⟨p, inferInstance⟩ ∧ l.length = p.primeHeight :=
  sorry

-- TODO: remove this in favour of `IsLocalization.primeHeight_eq_ringKrullDim`
/-- The height of a prime ideal `p` equals to the dimension of `A` localized away from `p`. -/
lemma Ideal.primeHeight_eq_ringKrullDim (p : Ideal A) [p.IsPrime] :
    p.primeHeight = ringKrullDim (Localization.AtPrime p) :=
  sorry


section

#check PrimeSpectrum.equivSubtype
#check IsLocalization.AtPrime.orderIsoOfPrime
#check Order.krullDim_eq_of_orderIso
#check Subtype.strictMono_coe

def PrimeSpectrum.orderIso (R : Type*) [CommSemiring R] :
    PrimeSpectrum R ≃o { q : Ideal R // q.IsPrime } :=
  Equiv.toOrderIso (PrimeSpectrum.equivSubtype R)
  (fun _ _ hle ↦ hle) (fun _ _ hle ↦ hle)

def PrimeSpectrum.orderIsoOfProp (R : Type*) [CommSemiring R] (motive : Ideal R → Prop) :
    { q : PrimeSpectrum R // motive q.asIdeal } ≃o { q : Ideal R // q.IsPrime ∧ motive q} where
  toFun q := ⟨q.val.asIdeal, ⟨q.val.isPrime, q.prop⟩⟩
  invFun q := ⟨⟨q, q.prop.1⟩, q.prop.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro p q
    rfl

def IsLocalization.AtPrime.orderIsoOfPrimeSpectrum {R : Type*} [CommSemiring R] (S : Type*)
    [CommSemiring S] [Algebra R S] (p : Ideal R) [hp : p.IsPrime] [IsLocalization.AtPrime S p] :
    PrimeSpectrum S ≃o { q : PrimeSpectrum R // q ≤ ⟨p, hp⟩ } :=
  OrderIso.trans
  (OrderIso.trans (PrimeSpectrum.orderIso S) (IsLocalization.AtPrime.orderIsoOfPrime S p))
  (PrimeSpectrum.orderIsoOfProp R (fun I ↦ (I ≤ p))).symm

end

section

#check Order.krullDim_le_of_strictMono
#check Order.height_le_height_apply_of_strictMono

variable {α : Type u_1} {s : Set α} [Preorder α] (a : α)

theorem chainHeight_eq_krullDim (hs : Nonempty s): s.chainHeight = Order.krullDim s := sorry
theorem chainHeight_le_eq_height : Set.chainHeight {b | b ≤ a} = Order.height a := sorry

def LTSeries.SubtypeLeEquivLastLe :
    LTSeries { b // b ≤ a } ≃ { p : LTSeries α // RelSeries.last p ≤ a } where
  toFun p := ⟨LTSeries.map p (fun b ↦ b.val) (Subtype.strictMono_coe _), by
    rw [LTSeries.last_map]
    exact (RelSeries.last p).prop⟩
  invFun p := {
    length := p.val.length
    toFun n := ⟨p.val.toFun n, by
      apply le_trans
      · exact LTSeries.monotone _ <| Fin.le_last n
      · exact p.prop
    ⟩
    step _ := p.val.step _
  }
  left_inv p := rfl
  right_inv p := rfl

lemma LTSeries.SubtypeLeEquivLastLe_length (p : LTSeries { b // b ≤ a }) :
    (LTSeries.SubtypeLeEquivLastLe a p).val.length = p.length :=
  rfl

lemma LTSeries.SubtypeLeEquivLastLe_symm_length (p : { p : LTSeries α // RelSeries.last p ≤ a }) :
    ((LTSeries.SubtypeLeEquivLastLe a).symm p).length = p.val.length :=
  rfl

lemma LTSeries.SubtypeLeEquivLastLe_head (p : LTSeries { b // b ≤ a }) :
    RelSeries.head (LTSeries.SubtypeLeEquivLastLe a p).val = RelSeries.head p :=
  rfl

lemma LTSeries.SubtypeLeEquivLastLe_symm_head (p : { p : LTSeries α // RelSeries.last p ≤ a }) :
    RelSeries.head ((LTSeries.SubtypeLeEquivLastLe a).symm p) = RelSeries.head p.val :=
  rfl

lemma LTSeries.SubtypeLeEquivLastLe_last (p : LTSeries { b // b ≤ a }) :
    RelSeries.last (LTSeries.SubtypeLeEquivLastLe a p).val = RelSeries.last p :=
  rfl

lemma LTSeries.SubtypeLeEquivLastLe_symm_last (p : { p : LTSeries α // RelSeries.last p ≤ a }) :
    RelSeries.last ((LTSeries.SubtypeLeEquivLastLe a).symm p) = RelSeries.last p.val :=
  rfl

theorem Order.hieght_eq_krullDim_le : Order.height a = Order.krullDim {b // b ≤ a} := by

  haveI : Nonempty { b // b ≤ a } := by
    use a
  rw [Order.krullDim_eq_iSup_length, WithBot.coe_inj, Order.height]
  apply le_antisymm
  · simp only [iSup_le_iff]
    intro p hp
    rw [← LTSeries.SubtypeLeEquivLastLe_symm_length a ⟨p, hp⟩]
    exact le_iSup_iff.mpr fun _ h ↦ h ((LTSeries.SubtypeLeEquivLastLe a).symm ⟨p, hp⟩)
  · rw [iSup_le_iff]
    intro p
    rw [← LTSeries.map_length p (fun b ↦ b.val) (Subtype.strictMono_coe _)]
    apply Order.length_le_height
    rw [LTSeries.last_map _ _ _]
    exact (RelSeries.last p).prop

end



/-- If `B = Aₚ`, `dim B = ht(p)`. -/
lemma IsLocalization.primeHeight_eq_ringKrullDim (p : Ideal A) [hp : p.IsPrime]
    [Algebra A B] [IsLocalization.AtPrime B p] :
    p.primeHeight = ringKrullDim B := by
  unfold ringKrullDim
  rw [Order.krullDim_eq_of_orderIso (IsLocalization.AtPrime.orderIsoOfPrimeSpectrum _ p),
    ← Order.hieght_eq_krullDim_le (⟨p, hp⟩ : PrimeSpectrum A),
    Ideal.primeHeight_eq_orderheight ]




-- TODO
/-- `dim A ≤ n` if and only if the height of all prime ideals is less than `n`. -/
lemma ringKrullDim_le_of_height_le [Nontrivial A] (n : WithBot (WithTop ℕ)) :
  ringKrullDim A ≤ n ↔
    ∀ (p : Ideal A), p.IsPrime → p.primeHeight ≤ n := by
  constructor
  · intro h p hp
    rw [WithBot.coe_eq_coe.mpr (Ideal.primeHeight_eq_orderheight p)]
    exact Preorder.le_trans _ _ n (Order.height_le_krullDim (⟨p, hp⟩ : PrimeSpectrum A)) h
  · intro h
    simp only [ringKrullDim, Order.krullDim, iSup_le_iff]
    intro l
    have := h l.last.asIdeal l.last.isPrime
    rw [Ideal.primeHeight_eq_orderheight, Order.height] at this
    have : (⨆ q : LTSeries (PrimeSpectrum A), ⨆ (_ : q.last ≤ l.last), (q.length : WithBot (WithTop ℕ))) ≤ n := by
      apply le_trans (by
        simp only [iSup_le_iff]
        exact fun q hq ↦ WithBot.coe_le_coe.mpr <| le_iSup_of_le q <| le_iSup_of_le hq <| by rfl) this
    exact iSup_le_iff.mp (iSup_le_iff.mp this l) (by rfl)

lemma Ideal.exists_isMaximal_height_eq_of_nontrivial [Nontrivial A] [FiniteDimensionalOrder (PrimeSpectrum A)] :
    ∃ (p : Ideal A), p.IsMaximal ∧ p.primeHeight = ringKrullDim A := by
  have := Order.krullDim_eq_length_of_finiteDimensionalOrder (α := (PrimeSpectrum A))
  unfold ringKrullDim
  rw [Order.krullDim_eq_length_of_finiteDimensionalOrder]
  set l := LTSeries.longestOf (PrimeSpectrum A)
  use l.last.asIdeal
  constructor
  · obtain ⟨m, maxm, hm⟩ := Ideal.exists_le_maximal l.last.asIdeal IsPrime.ne_top'
    by_cases h : l.last.asIdeal = m
    · exact h ▸ maxm
    have eq := RelSeries.snoc_length l ⟨m, maxm.isPrime⟩ (lt_of_le_of_ne hm <| ne_of_apply_ne _ h)
    have le := LTSeries.longestOf_is_longest <| RelSeries.snoc l ⟨m, maxm.isPrime⟩ (lt_of_le_of_ne hm <| ne_of_apply_ne _ h)
    rw [eq] at le
    exact False.elim (Nat.not_succ_le_self _ le)
  rw [Ideal.primeHeight_eq_orderheight, Order.height]
  apply WithBot.coe_eq_coe.mpr
  apply le_antisymm
  · simp only [iSup_le_iff, Nat.cast_le]
    exact fun q hq ↦ LTSeries.longestOf_is_longest q
  exact le_iSup_iff.mpr <| fun _ h ↦ iSup_le_iff.mp (h l) (by rfl)

lemma height_eq_of_ringEquiv (e : A ≃+* B) (p : Ideal A) [hp : p.IsPrime] :
    (p.map e).primeHeight = p.primeHeight := by
  repeat rw [Ideal.primeHeight_eq_orderheight]
  set g := PrimeSpectrum.comapEquiv e
  have eq : Ideal.map e p = Ideal.comap e.symm p := Ideal.map_comap_of_equiv e
  set f : PrimeSpectrum A ≃o PrimeSpectrum B := { g with
    map_rel_iff' := by
      intro a b
      unfold g PrimeSpectrum.comapEquiv RingHom.specComap
      simp only [RingEquiv.toRingHom_eq_coe, Equiv.coe_fn_mk, ← PrimeSpectrum.asIdeal_le_asIdeal,
        ← Ideal.map_le_iff_le_comap, Ideal.map_comap_of_equiv, RingEquiv.symm_symm]
      apply Iff.of_eq
      congr
      calc
        _ = Ideal.comap e.toRingHom (Ideal.comap (e.symm.toRingHom) a.asIdeal) := by rfl
        _ = _ := by simp only [Ideal.comap_comap, RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp, Ideal.comap_id] }
  rw [← Order.height_orderIso f ⟨p, hp⟩]
  congr

lemma IsLocalization.height_eq_of_disjoint [Algebra A B] (M : Submonoid A)
    [IsLocalization M B] (p : Ideal A) [hp : p.IsPrime] (h : Disjoint (M : Set A) (p : Set A)) :
    (p.map <| algebraMap A B).primeHeight = p.primeHeight := by
  letI := IsLocalization.isPrime_of_isPrime_disjoint M B p hp h
  set P := p.map (algebraMap A B)
  letI := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (M := M) (Localization.AtPrime P) P
  have eq := comap_map_of_isPrime_disjoint M B p hp h
  simp only [eq] at this
  have := ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime P) (Localization.AtPrime p)).toRingEquiv
  rw [← IsLocalization.primeHeight_eq_ringKrullDim P, ← IsLocalization.primeHeight_eq_ringKrullDim p] at this
  exact WithBot.coe_eq_coe.mp this
