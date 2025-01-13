import Mathlib

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The height of a prime ideal in a ring is the supremum over the lengths of prime ideal
chains ending at `p`. -/
noncomputable def Ideal.primeHeight (p : Ideal A) : WithTop ℕ :=
  Set.chainHeight { q : Ideal A | q.IsPrime ∧ q ≤ p }

lemma chainHeight_eq_orderHeight {α : Type*} [Preorder α] (p : α) :
    Set.chainHeight { q : α | q ≤ p } = Order.height p := by
  sorry

lemma Ideal.primeHeight_eq_orderheight (p : Ideal A) [hp : p.IsPrime] :
    Ideal.primeHeight p = Order.height (⟨p, hp⟩ : PrimeSpectrum A) := by
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
lemma IsLocalization.primeHeight_eq_ringKrullDim (p : Ideal A) [p.IsPrime]
    [Algebra A B] [IsLocalization.AtPrime B p] :
    p.primeHeight = ringKrullDim B :=
  sorry

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
    by_cases ht : n = ⊤
    · exact ht ▸ OrderTop.le_top (ringKrullDim A)
    by_cases hb : n = ⊥
    · obtain ⟨p, hp⟩ := Ideal.exists_maximal A
      have := h p hp.isPrime
      simp only [hb, le_bot_iff, WithBot.coe_ne_bot] at this
    by_contra! hlt
    by_cases hab : ringKrullDim A = ⊥
    · simp only [hab, not_lt_bot] at hlt
    obtain ⟨n1, hn1⟩ := WithBot.ne_bot_iff_exists.mp hb
    obtain ⟨m1, hm1⟩ := WithBot.ne_bot_iff_exists.mp hab
    rw [← hn1, WithBot.coe_eq_top] at ht
    obtain ⟨n2, hn2⟩ := WithTop.ne_top_iff_exists.mp ht
    rw [← hn1, ← hm1, WithBot.coe_lt_coe] at hlt
    have : n + 1 ≤ ringKrullDim A := by
      by_cases hat : ringKrullDim A = ⊤
      · exact hat ▸ OrderTop.le_top (n + 1)
      rw [← hm1, WithBot.coe_eq_top] at hat
      obtain ⟨m2, hm2⟩ := WithTop.ne_top_iff_exists.mp hat
      rw [← hn2, ← hm2, ENat.some_eq_coe, Nat.cast_lt] at hlt
      rw [← hm1, ← hn1, ← WithBot.coe_one, ← WithBot.coe_add n1 1, ← hn2, ← hm2, ← WithTop.coe_one, ← WithTop.coe_add n2 1]
      refine WithBot.coe_le_coe.mpr <| WithTop.coe_le_coe.mpr hlt
    rw [ringKrullDim, ← hn1, ← WithBot.coe_one, ← WithBot.coe_add n1 1, ← hn2, ← WithTop.coe_one, ← WithTop.coe_add n2 1] at this
    obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp this
    have := h l.last.asIdeal l.last.isPrime
    rw [Ideal.primeHeight_eq_orderheight, ← hn1, WithBot.coe_le_coe, Order.height_le_iff] at this
    have := this (p := l) (by rfl)
    rw [hl, ← hn2, ENat.some_eq_coe, Nat.cast_le] at this
    have : n2 + 1 ≤ n2 := this
    simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero] at this

lemma Ideal.exists_isMaximal_height_eq_of_nontrivial [Nontrivial A] :
    ∃ (p : Ideal A), p.IsMaximal ∧ p.primeHeight = ringKrullDim A :=
  sorry

lemma height_eq_of_ringEquiv (e : A ≃+* B) (p : Ideal A) [p.IsPrime] :
    (p.map e).primeHeight = p.primeHeight :=
  sorry

lemma IsLocalization.height_eq_of_disjoint [Algebra A B] (M : Submonoid A)
    [IsLocalization M B] (p : Ideal A) [p.IsPrime] (h : Disjoint (M : Set A) (p : Set A)) :
    (p.map <| algebraMap A B).primeHeight = p.primeHeight :=
  sorry
