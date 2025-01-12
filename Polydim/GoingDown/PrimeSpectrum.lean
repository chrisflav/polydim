import Mathlib

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
   (M : Submonoid R) [IsLocalization M S] (I : Ideal R)

lemma IsLocalization.algebraMap_mem_comap_iff (x : R) :
    algebraMap R S x ∈ I.map (algebraMap R S) ↔
      ∃ m ∈ M, x * m ∈ I := by
  refine ⟨fun hx ↦ ?_, fun ⟨m, hm, hx⟩ ↦ ?_⟩
  · rw [IsLocalization.mem_map_algebraMap_iff M] at hx
    obtain ⟨⟨a, m⟩, hx⟩ := hx
    rw [← map_mul] at hx
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M S).1 hx
    refine ⟨c * m, M.mul_mem c.2 m.2, ?_⟩
    · have : x * (↑c * ↑m) = ↑c * (x * ↑m) := by ring
      rw [this, hc]
      exact I.mul_mem_left _ a.2
  · rw [IsLocalization.mem_map_algebraMap_iff M]
    use ⟨⟨x * m, hx⟩, ⟨m, hm⟩⟩
    simp

lemma IsLocalization.comap_map :
    (I.map (algebraMap R S)).comap (algebraMap R S) =
      ⨆ m ∈ M, Submodule.colon I (Ideal.span {m}) := by
  have : (Ideal.comap (algebraMap R S) (Ideal.map (algebraMap R S) I) : Set R) =
      ⋃ m ∈ M, Submodule.colon I (Ideal.span {m}) := by
    ext x
    simpa using IsLocalization.algebraMap_mem_comap_iff M I x
  have : (Ideal.comap (algebraMap R S) (Ideal.map (algebraMap R S) I) : Set R) =
      ((⨆ m ∈ M, Submodule.colon I (Ideal.span {m}) : Ideal R) : Set R) := by
    apply le_antisymm
    · rw [this]
      sorry
    · sorry
  rw [Set.ext_iff] at this
  simp at this
  ext x
  simp
  rw [this]

lemma IsLocalization.map_ne_top_iff_disjoint :
    I.map (algebraMap R S) ≠ ⊤ ↔ Disjoint (M : Set R) (I : Set R) := by
  simp only [ne_eq, Ideal.eq_top_iff_one, ← map_one (algebraMap R S), not_iff_comm,
    IsLocalization.algebraMap_mem_comap_iff M]
  simp [Set.disjoint_left]

end

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

/-- `p` is in the image of `Spec S → Spec R` if and only if `p` extended to `S` and
restricted back to `R` is `p`. -/
lemma PrimeSpectrum.mem_range_comap_iff (p : PrimeSpectrum R) :
    p ∈ Set.range (PrimeSpectrum.comap f) ↔ (p.asIdeal.map f).comap f = p.asIdeal := by
  refine ⟨?_, fun hp ↦ ?_⟩
  · rintro ⟨q, rfl⟩
    simp
  · let M : Submonoid S := Submonoid.map f p.asIdeal.primeCompl
    have : (p.asIdeal.map f).map (algebraMap S (Localization M)) ≠ ⊤ := by
      rw [IsLocalization.map_ne_top_iff_disjoint M, Set.disjoint_left]
      rintro a ⟨x, (hx : x ∉ p.asIdeal), rfl⟩
      rwa [← hp] at hx
    obtain ⟨m, _, hle⟩ := Ideal.exists_le_maximal _ this
    let q : Ideal S := m.comap (algebraMap S (Localization M))
    have hd : Disjoint (M : Set S) (q : Set S) :=
      ((IsLocalization.isPrime_iff_isPrime_disjoint M _ m).mp inferInstance).right
    have h1 : q.comap f ≤ p.asIdeal := by
      simp only [Submonoid.coe_map, M, Set.disjoint_right] at hd
      intro x (hx : x ∈ f ⁻¹' q)
      have : x ∉ p.asIdeal.primeCompl := by
        intro ha
        apply hd hx
        simp only [Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
        use x
      simpa [Ideal.primeCompl] using this
    have h2 : p.asIdeal ≤ q.comap f := by
      rw [← hp, ← Ideal.map_le_iff_le_comap, Ideal.map_comap_map, ]
      simpa only [q, ← Ideal.map_le_iff_le_comap]
    exact ⟨⟨q, inferInstance⟩, le_antisymm h1 h2⟩
