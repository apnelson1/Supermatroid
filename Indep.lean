import Supermatroid.Basic

open OrderDual Set

variable {α : Type*} {a b c x y z i j s t : α}

namespace Supermatroid

variable [Lattice α] [Supermatroid α]

section Indep

/-- An `Indep`endent set is one cospanned by everything below it. -/
def Indep (i : α) := ∀ ⦃j⦄, j ≤ i → j ≤₁ i

lemma exists_indep (α : Type*) [Lattice α] [Supermatroid α] : ∃ (i : α), Indep i := by
  obtain ⟨i, hi⟩ := Supermatroid.exists_indep' (α := α)
  refine ⟨i, fun x hix ↦ ?_⟩
  obtain (rfl | hlt) := hix.eq_or_lt
  · exact CospansLE.refl
  exact hi _ hlt

lemma indep_iff_forall_cospansLE : Indep i ↔ ∀ ⦃j⦄, j ≤ i → j ≤₁ i := Iff.rfl

lemma Indep.cospansLE_of_le (hi : Indep i) (hji : j ≤ i) : j ≤₁ i :=
  hi hji

lemma Indep.mono (hi : Indep i) (hji : j ≤ i) : Indep j :=
  fun _ hkj ↦ (hi (hkj.trans hji)).mono_right hkj hji

lemma Indep.inf_left (hi : Indep i) (x : α) : Indep (x ⊓ i) :=
  hi.mono inf_le_right

lemma Indep.inf_right (hi : Indep i) (x : α) : Indep (i ⊓ x) :=
  hi.mono inf_le_left

lemma Indep.mono_cospansLE (hi : Indep i) (hij : i ≤₁ j) : Indep j :=
  fun _ hkj ↦ ((hi.cospansLE_of_le inf_le_left).trans hij).mono_left inf_le_right hkj

lemma bot_indep [OrderBot α] : Indep (⊥ : α) := by
  simp [Indep, CospansLE.refl]

@[simp] lemma bot_cospansLE_iff [OrderBot α] : ⊥ ≤₁ i ↔ Indep i :=
  ⟨bot_indep.mono_cospansLE, fun h ↦ h.cospansLE_of_le bot_le⟩

lemma indep_iff_bot_spans [OrderBot α] : Indep i ↔ ⊥ ≤₁ i := by
  rw [indep_iff_forall_cospansLE]
  exact ⟨fun h ↦ h bot_le, fun h j hji ↦ h.mono_left bot_le hji⟩

end Indep

section Spanning

/-- A `Spanning` set is one that spans everything above it. -/
def Spanning (s : α) := ∀ ⦃t⦄, s ≤ t → s ≤₀ t

lemma spanning_iff_forall_spansLE : Spanning s ↔ ∀ ⦃t⦄, s ≤ t → s ≤₀ t := Iff.rfl

lemma Spanning.spansLE_of_le (hs : Spanning s) (hst : s ≤ t) : s ≤₀ t :=
  hs hst

@[simp] lemma dual_indep_iff {i : αᵒᵈ} : Indep i ↔ Spanning (ofDual i) := Iff.rfl

@[simp] lemma dual_spanning_iff {s : αᵒᵈ} : Spanning s ↔ Indep (ofDual s) := Iff.rfl

@[simp] lemma toDual_indep_iff : Indep (toDual i) ↔ Spanning i := Iff.rfl

@[simp] lemma toDual_spanning_iff : Spanning (toDual i) ↔ Indep i := Iff.rfl

lemma exists_spanning (α : Type*) [Lattice α] [Supermatroid α] : ∃ (s : α), Spanning s :=
  exists_indep αᵒᵈ

lemma Indep.spanning_toDual (hi : Indep i) : Spanning (toDual i) :=
  hi

lemma Spanning.indep_toDual (hs : Spanning s) : Indep (toDual s) :=
  hs

lemma Spanning.mono (hs : Spanning s) (hst : s ≤ t) : Spanning t :=
  hs.indep_toDual.mono hst

lemma Spanning.sup_left (hs : Spanning s) (x : α) : Spanning (x ⊔ s) :=
  hs.mono le_sup_right

lemma Spanning.sup_right (hs : Spanning s) (x : α) : Spanning (s ⊔ x) :=
  hs.mono le_sup_left

lemma Spanning.mono_spansLE (hs : Spanning s) (hts : t ≤₀ s) : Spanning t :=
  hs.indep_toDual.mono_cospansLE hts

lemma top_spanning [OrderTop α] : Spanning (⊤ : α) :=
  bot_indep (α := αᵒᵈ)

lemma Spanning.eq_of_le_indep (hs : Spanning s) (hi : Indep i) (hsi : s ≤ i) : s = i :=
  (hi.cospansLE_of_le hsi).eq_of_spansLE <| hs.spansLE_of_le hsi

@[simp] lemma spansLE_top_iff [OrderTop α] : s ≤₀ ⊤ ↔ Spanning s :=
  bot_cospansLE_iff (α := αᵒᵈ)

end Spanning

section IsBase

/-- A `IsBase` is an independent spanning set. -/
def IsBase (b : α) := Indep b ∧ Spanning b

lemma isBase_def : IsBase b ↔ Indep b ∧ Spanning b := Iff.rfl

@[simp] lemma dual_isBase_iff {b : αᵒᵈ} : IsBase b ↔ IsBase (ofDual b) :=
  And.comm

@[simp] lemma toDual_isBase_iff : IsBase (toDual b) ↔ IsBase b :=
  And.comm

lemma IsBase.indep (hb : IsBase b) : Indep b :=
  hb.1

lemma IsBase.spanning (hb : IsBase b) : Spanning b :=
  hb.2

lemma Indep.isBase_of_spanning (hi : Indep b) (hs : Spanning b) : IsBase b := ⟨hi, hs⟩

lemma Spanning.isBase_of_indep (hs : Spanning b) (hi : Indep b) : IsBase b := ⟨hi, hs⟩

lemma IsBase.isBase_toDual (hb : IsBase b) : IsBase (toDual b) :=
  toDual_isBase_iff.2 hb

lemma Indep.exists_le_isBase_of_le_of_spanning (hi : Indep i) (hs : Spanning s) (hle : i ≤ s) :
    ∃ b, IsBase b ∧ i ≤ b ∧ b ≤ s := by
  obtain ⟨b, hib, hbs⟩ := exists_cospansLE_spansLE_of_le hle
  exact ⟨b, ⟨hi.mono_cospansLE hib, hs.mono_spansLE hbs⟩, hib.le, hbs.le⟩

lemma Indep.exists_le_isBase (hi : Indep i) : ∃ b, IsBase b ∧ i ≤ b := by
  obtain ⟨s, hs⟩ := exists_spanning α
  obtain ⟨b, hb, hib, -⟩ := hi.exists_le_isBase_of_le_of_spanning (hs.mono le_sup_right) le_sup_left
  exact ⟨b, hb, hib⟩

lemma Spanning.exists_isBase_le (hs : Spanning s) : ∃ b, IsBase b ∧ b ≤ s := by
  simp_rw [isBase_def, and_comm (a := Indep _)]
  exact Indep.exists_le_isBase (α := αᵒᵈ) hs

lemma IsBase.eq_of_le_indep (hb : IsBase b) (hbi : b ≤ i) (hi : Indep i) : b = i :=
  (hb.2.spansLE_of_le hbi).eq_of_cospansLE <| hi.cospansLE_of_le hbi

lemma IsBase.eq_of_spanning_le (hb : IsBase b) (hsb : s ≤ b) (hs : Spanning s) : b = s :=
  Eq.symm <| (hb.1.cospansLE_of_le hsb).eq_of_spansLE <| hs.spansLE_of_le hsb

lemma exists_isBase : ∃ (b : α), IsBase b := by
  obtain ⟨i, hi : Indep i⟩ := exists_indep (α := α)
  obtain ⟨s, hs : Spanning s⟩ := exists_spanning (α := α)
  obtain ⟨b, hb, -, -⟩ :=
    (hi.mono inf_le_left).exists_le_isBase_of_le_of_spanning (hs.mono le_sup_right) inf_le_sup
  exact ⟨b, hb⟩

end IsBase

section IsBasis

/-- A `IsBasis` for `x` is an independent element below `x` that spans `x`. -/
@[mk_iff]
structure IsBasis (i x : α) : Prop where
  indep : Indep i
  spansLE : i ≤₀ x

lemma IsBasis.le (h : IsBasis i x) : i ≤ x :=
  h.2.le

lemma Indep.isBasis_of_spansLE (hi : Indep i) (hix : i ≤₀ x) : IsBasis i x :=
  ⟨hi, hix⟩

lemma Indep.isBasis_self (hi : Indep i) : IsBasis i i :=
  hi.isBasis_of_spansLE SpansLE.refl

lemma IsBasis.eq_of_le_indep (h : IsBasis i x) (hj : Indep j) (hij : i ≤ j) (hjx : j ≤ x) : i = j :=
  (h.spansLE.mono_right hij hjx).eq_of_cospansLE <| hj.cospansLE_of_le hij


lemma isBasis_iff_maximal_indep : IsBasis i x ↔ Maximal (fun i ↦ Indep i ∧ i ≤ x) i := by
  refine ⟨fun h ↦ ⟨⟨h.indep, h.le⟩, fun j hj hij ↦ (h.eq_of_le_indep hj.1 hij hj.2).ge⟩,
    fun h ↦ ⟨h.1.1, ?_⟩⟩
  obtain ⟨k, hik, hkx⟩ := exists_cospansLE_spansLE_of_le h.1.2
  rwa [← h.eq_of_ge ⟨h.1.1.mono_cospansLE hik, hkx.le⟩ hik.le]

lemma Indep.isBasis_of_maximal (hi : Indep i) (hix : i ≤ x)
    (hmax : ∀ j, Indep j → i ≤ j → j ≤ x → j ≤ i) : IsBasis i x := by
  rw [isBasis_iff_maximal_indep, Maximal, and_iff_right hi, and_iff_right hix]
  exact fun y ⟨hy, hyx⟩ hiy ↦ hmax y hy hiy hyx

lemma Indep.exists_le_isBasis_of_le (hi : Indep i) (hix : i ≤ x) : ∃ j, IsBasis j x ∧ i ≤ j :=
  let ⟨j, hij, hjx⟩ := exists_cospansLE_spansLE_of_le hix
  ⟨j, (hi.mono_cospansLE hij).isBasis_of_spansLE hjx, hij.le⟩

@[simp] lemma isBasis_top_iff [OrderTop α] : IsBasis b ⊤ ↔ IsBase b := by
  rw [isBasis_iff, spansLE_top_iff, isBase_def]

lemma exists_isBasis (x : α) : ∃ i, IsBasis i x := by
  obtain ⟨j, hj⟩ := exists_indep α
  obtain ⟨i, hi, -⟩ := (hj.mono (inf_le_left (b := x))).exists_le_isBasis_of_le inf_le_right
  exact ⟨i, hi⟩

lemma IsBasis.spansLE_iff_isBasis_le (hix : IsBasis i x) : x ≤₀ y ↔ IsBasis i y ∧ x ≤ y :=
  ⟨fun h ↦ ⟨⟨hix.indep, hix.spansLE.trans h⟩, h.le⟩, fun h ↦ h.1.2.mono_left hix.le h.2⟩

lemma spansLE_iff_forall_isBasis : x ≤₀ y ↔ x ≤ y ∧ ∀ i, IsBasis i x → IsBasis i y := by
  refine ⟨fun h ↦ ⟨h.le, fun i hix ↦ ⟨hix.1, hix.2.trans h⟩⟩, fun ⟨hle, h⟩ ↦ ?_⟩
  obtain ⟨i, hix⟩ := exists_isBasis x
  exact hix.spansLE_iff_isBasis_le.2 ⟨h _ hix, hle⟩

lemma IsBasis.sup [IsModularLattice α] (hix : IsBasis i x) (hiy : IsBasis i y) :
    IsBasis i (x ⊔ y) := by
  rw [isBasis_iff] at *
  exact ⟨hix.1, hix.2.sup hiy.2⟩

end IsBasis

section IsCanopy

/-- A `IsCanopy` for `x` is a spanning element cospanned by `x`. -/
@[mk_iff]
structure IsCanopy (s x : α) : Prop where
  spanning : Spanning s
  cospansLE : x ≤₁ s

lemma IsCanopy.le (h : IsCanopy s x) : x ≤ s :=
  h.2.le

@[simp]
lemma dual_isBasis_iff {i x : αᵒᵈ} : IsBasis i x ↔ IsCanopy (ofDual i) (ofDual x) := by
  rw [isBasis_iff, isCanopy_iff, dual_indep_iff]
  rfl

@[simp]
lemma toDual_isBasis_iff : IsBasis (toDual i) (toDual x) ↔ IsCanopy i x := by
  simp [isBasis_iff, isCanopy_iff]

@[simp]
lemma dual_isCanopy_iff {s x : αᵒᵈ} : IsCanopy s x ↔ IsBasis (ofDual s) (ofDual x) := by
  simp [isCanopy_iff, isBasis_iff]

@[simp]
lemma toDual_isCanopy_iff : IsCanopy (toDual s) (toDual x) ↔ IsBasis s x := by
  simp [isCanopy_iff, isBasis_iff]

alias ⟨_, IsBasis.isCanopy_toDual⟩ := toDual_isCanopy_iff

alias ⟨_, IsCanopy.isBasis_toDual⟩ := toDual_isBasis_iff

lemma IsCanopy.eq_of_spanning_le (hsx : IsCanopy s x) (ht : Spanning t) (hts : t ≤ s)
    (hxt : x ≤ t) : s = t := by
  simpa using hsx.isBasis_toDual.eq_of_le_indep ht.indep_toDual (by simpa) (by simpa)

lemma Spanning.exists_isCanopy_le_of_le (hs : Spanning s) (hxs : x ≤ s) :
    ∃ t, IsCanopy t x ∧ t ≤ s := by
  simpa using hs.indep_toDual.exists_le_isBasis_of_le (x := toDual x) (by simpa)

lemma Spanning.isCanopy_of_minimal_ (hs : Spanning s) (hxs : x ≤ s)
    (h : ∀ t, Spanning t → t ≤ s → x ≤ t → s ≤ t) : IsCanopy s x := by
  simpa using hs.indep_toDual.isBasis_of_maximal (x := toDual x) hxs h

lemma isCanopy_bot_iff [OrderBot α] : IsCanopy b ⊥ ↔ IsBase b := by
  rw [isCanopy_iff, bot_cospansLE_iff, isBase_def, and_comm]

lemma exists_isCanopy (x : α) : ∃ s, IsCanopy s x := by
  obtain ⟨b, hb⟩ := exists_isBasis (toDual x)
  exact ⟨ofDual b, by simpa using hb⟩

lemma IsCanopy.cospansLE_iff_isCanopy_le (hsy : IsCanopy s y) : x ≤₁ y ↔ IsCanopy s x ∧ x ≤ y := by
  simpa using hsy.isBasis_toDual.spansLE_iff_isBasis_le (y := toDual x)

lemma cospansLE_iff_forall_isCanopy : x ≤₁ y ↔ x ≤ y ∧ ∀ s, IsCanopy s y → IsCanopy s x := by
  simpa using spansLE_iff_forall_isBasis (x := toDual y) (y := toDual x)

end IsCanopy

lemma Indep.cospans (hi : Indep i) (x : α) : x ⇒₁ i :=
  hi.cospansLE_of_le inf_le_right

@[simp] lemma bot_cospans_iff [OrderBot α] : ⊥ ⇒₁ i ↔ Indep i := by
  simp [cospans_iff_inf_cospansLE_left]

lemma Spanning.spans (hs : Spanning s) (x : α) : s ⇒₀ x :=
  hs.spansLE_of_le le_sup_right

lemma Spans.spanning_of_spanning [IsModularLattice α] (hts : t ⇒₀ s) (hs : Spanning s) :
    Spanning t :=
  fun r htr ↦ (hts.trans (hs.spans r)).spansLE_of_le htr

@[simp] lemma spans_top_iff [OrderTop α] : s ⇒₀ ⊤ ↔ Spanning s := by
  simp [spans_iff_spansLE_sup_left]

lemma Cospans.indep_of_indep [IsModularLattice α] (hij : i ⇒₁ j) (hi : Indep i) : Indep j :=
  hij.toDual_spans.spanning_of_spanning hi

end Supermatroid
