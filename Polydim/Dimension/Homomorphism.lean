import Mathlib
import Polydim.Dimension.Height
import Polydim.Dimension.NoetherianLocal
import Polydim.GoingDown.GoingDown

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [IsNoetherianRing B]

instance (p : Ideal A) [p.IsPrime] : IsNoetherianRing (Localization.AtPrime p) := by
  apply IsLocalization.isNoetherianRing p.primeCompl
  infer_instance

/-- Matsumura 13.B Th. 19 (2). This holds more generally for any `A`-algebra `B` that satisfies
going-down. -/
lemma primeHeight_eq_primeHeight_add_of_liesOver_of_flat [Module.Flat A B] (p : Ideal A) [p.IsPrime]
    (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    P.primeHeight = p.primeHeight +
      (P.map (Ideal.Quotient.mk <| p.map (algebraMap A B))).primeHeight := by
  -- use `primeHeight_le_primeHeight_add_of_liesOver` for one direction
  -- and going down for the other one
  apply le_antisymm
  · apply primeHeight_le_primeHeight_add_of_liesOver
  · wlog h : P.primeHeight ≠ ⊤
    · simp only [ne_eq, Decidable.not_not] at h
      rw [h]
      simp
    obtain ⟨lp, hlp, hlenp⟩ := p.exists_series_of_primeHeight_ne_top p.primeHeight_ne_top_of_isNoetherianRing
    have : (Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap A B) p)) P).IsPrime := by
      apply Ideal.map_quotient_mk_isPrime_of_isPrime
      rw [Ideal.map_le_iff_le_comap]
      rw [Ideal.LiesOver.over (p := p) (P := P), Ideal.under_def]
    obtain ⟨lq, hlq, hlenq⟩ :=
      (Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap A B) p)) P).exists_series_of_primeHeight_ne_top
        (Ideal.primeHeight_ne_top_of_isNoetherianRing _)
    rw [← hlenp, ← hlenq]
    let f :=
      (Ideal.Quotient.mk (Ideal.map (algebraMap A B) p)).specComap
    have hf : StrictMono f := by
      intro x y hxy
      exact (Ideal.relIsoOfSurjective
        (Ideal.Quotient.mk <| p.map (algebraMap A B)) Ideal.Quotient.mk_surjective).strictMono hxy
    -- lift chain from the quotient
    let l' : LTSeries (PrimeSpectrum B) := lq.map f hf
    have : l'.head.asIdeal.LiesOver lp.last.asIdeal := by
      simp [l', hlp]
      constructor
      rw [Ideal.under_def]
      apply le_antisymm
      · rw [← Ideal.map_le_iff_le_comap]
        rw [← Ideal.map_le_iff_le_comap]
        simp
      · conv_rhs => rw [Ideal.LiesOver.over (p := p) (P := P), Ideal.under_def]
        apply Ideal.comap_mono
        apply le_trans
        · apply Ideal.comap_mono (lq.head_le_last)
        · rw [hlq]
          simp only [Ideal.comap_map_quotient_mk, sup_le_iff, le_refl, and_true]
          rw [Ideal.map_le_iff_le_comap]
          rw [Ideal.LiesOver.over (p := p) (P := P), Ideal.under_def]
    -- lifted via going-down using `hlo`
    obtain ⟨lp', hlp'len, hlp', _⟩ := Algebra.HasGoingDown.exists_ltSeries
        A B Algebra.HasGoingDown.of_flat lp l'.head.asIdeal
    let l : LTSeries (PrimeSpectrum B) := lp'.smash l' hlp'
    have : l.length = lp'.length + l'.length := by simp [l]
    simp [l', hlp'len] at this
    rw [← Nat.cast_add, ← this]
    rw [Ideal.primeHeight_eq_orderheight]
    apply Order.length_le_height
    simp [l, l', f, hlq]
    show _ ≤ P
    simp only [Ideal.comap_map_quotient_mk, sup_le_iff, le_refl, and_true]
    rw [Ideal.map_le_iff_le_comap]
    rw [Ideal.LiesOver.over (p := p) (P := P), Ideal.under_def]
