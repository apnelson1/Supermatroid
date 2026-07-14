import Mathlib.Order.Minimal
import LatticeMatroid.Supermatroid.Indep

/-
Here we give two alternative definitions for a `Supermatroid`.
The first `BaseSupermatroid`, is in terms of bases, and has self-dual axioms.
They look a little strange, but in the finite setting they specialize
to the usual matroid axioms without too much work, and the self-duality saves a lot of time.

The second, `IndepSupermatroid`, is a set of independence axioms that readily
specializes to the familiar ones for both matroids and q-matroids.

We show that `IndepSupermatroid ⇒ BaseSupermatroid ⇒ Supermatroid`. The reverse
direction would take a little extra work but shouldn't be too hard.

Since we are making a beeline towards the definition of a `Supermatroid`,
we do not provide extensive API for `IndepSupermatroid` or `BaseSupermatroid`;
this will be inherited from the API for `Supermatroid`.
Despite this, I have tried not to make things too terse.
Some lemmas that turned out not to be needed are commented out.

-/

open OrderDual

variable {α : Type*} {i j b x y z s t : α}





/-- A `BaseSupermatroid` is a supermatroid defined in terms of its bases.
The axiom set is self-dual.-/
class BaseSupermatroid (α : Type*) [Lattice α] where

  /-- A `Base` predicate-/
  (Base : α → Prop)

  /-- Bases are an antichain -/
  (antichain : IsAntichain (· ≤ ·) (setOf Base))

  /-- There is a base. This is equivalent to the assertion that `α` is nonempty. -/
  (exists_base : ∃ b, Base b)

  /-- Between any nested independent and spanning elements, there is a base. -/
  (exists_base_between_inf_sup :
    ∀ ⦃b₁ b₂ : α⦄, Base b₁ → Base b₂ → ∀ (x₁ x₂ : α),
      x₁ ⊓ b₁ ≤ x₂ ⊔ b₂ → ∃ b, Base b ∧ x₁ ⊓ b₁ ≤ b ∧ b ≤ x₂ ⊔ b₂)

  /-- `Frame b x` means that `b` is a base intersecting `x` in a basis for `x`.
    (This is not how we actually define it, but we'll prove it. ) -/
  (Frame : α → α → Prop)

  /-- We define `Frame b x` in a self-dual way.
  A base `b` is a `Frame` for `x` if every base `b'` in the interval `[x ⊓ b, x ⊔ b]`
  has the same sup and inf with `x` that `b` does. -/
  (frame_iff : ∀ ⦃b x⦄, Frame b x ↔ Base b ∧ ∀ b₁, Base b₁ → x ⊓ b ≤ b₁ → b₁ ≤ x ⊔ b →
    RelPerspective x b₁ b)

  /-- Every element has a frame. -/
  (exists_frame : ∀ x, ∃ b, Frame b x)

  /-- If `b` is a frame for `x` and `y` and `x,y` have the same inf and sup with `b`, then `x = y`.
  This encodes the 'no bad diamond' axiom that is typically needed for lattice definitions. -/
  (eq_of_frame_frame : ∀ ⦃x y b⦄, Frame b x → Frame b y → x ⊓ b = y ⊓ b →
    RelPerspective b x y → x = y)

namespace BaseSupermatroid

/-- A `BaseSupermatroid` gives a `BaseSupermatroid` on the dual lattice. This halves our work. -/
instance {α : Type*} [Lattice α] [BaseSupermatroid α] : BaseSupermatroid αᵒᵈ where
  Base b := Base <| ofDual b
  Frame b x := Frame (ofDual b) (ofDual x)
  exists_base := exists_base (α := α)
  frame_iff b x := by
    simp_rw [frame_iff, OrderDual.forall, ofDual_toDual, and_congr_right_iff]
    refine fun _ ↦ ⟨fun h b' hb' h1 h2 ↦ And.symm (h b' hb' h2 h1),
      fun h b' hb' h1 h2 ↦ And.symm (h b' hb' h2 h1)⟩
  antichain _ hb _ hb' hne := antichain (α := α) hb' hb hne.symm
  exists_base_between_inf_sup b₁ b₂ hb₁ hb₂ x₁ x₂ hle := by
    obtain ⟨b, hb, hleb, hble⟩ := exists_base_between_inf_sup (α := α) hb₂ hb₁ x₂ x₁ hle
    exact ⟨b, hb, hble, hleb⟩
  exists_frame x := exists_frame (ofDual x)
  eq_of_frame_frame x y b hx hy hi hu := (eq_of_frame_frame hy hx hu.symm hi.symm).symm

variable [Lattice α] [IsModularLattice α] [BaseSupermatroid α] {b' b₁ b₂ : α}

lemma Base.eq_of_le (hb : Base b) (hb' : Base b') (hle : b ≤ b') : b = b' :=
  antichain.eq hb hb' hle

lemma Base.toDual (h : Base b) : Base (toDual b) :=
  h

lemma Base.ofDual {b : αᵒᵈ} (h : Base b) : Base (ofDual b) :=
  h

@[simp] lemma base_dual_iff : Base (toDual b) ↔ Base b := Iff.rfl

-- lemma frame_def : Frame b x ↔ Base b ∧ ∀ b₁, Base b₁ → x ⊓ b ≤ b₁ → b₁ ≤ x ⊔ b →
--     x ⊓ b₁ = x ⊓ b ∧ x ⊔ b₁ = x ⊔ b := by rw [frame_iff]

lemma Frame.ofDual {b x : αᵒᵈ} (h : Frame b x) : Frame (ofDual b) (ofDual x) :=
  h

lemma Frame.toDual (h : Frame b x) : Frame (toDual b) (toDual x) :=
  h

@[simp] lemma frame_dual_iff : Frame (toDual b) (toDual x) ↔ Frame b x := Iff.rfl

lemma Frame.base (h : Frame b x) : Base b :=
  (frame_iff.1 h).1



lemma Base.frame_of_inf (hb : Base b) (h : ∀ b', Base b' → x ⊓ b ≤ b' → x ⊓ b' ≤ b) :
    Frame b x := by
  refine frame_iff.2 ⟨hb, fun b₁ hb₁ hleb₁ hb₁le ↦ ?_⟩
  obtain ⟨b', hb', hleb', hb'le⟩ := exists_base_between_inf_sup hb hb₁ (x ⊔ b₁) x inf_le_left
  obtain rfl : (x ⊔ b₁) ⊓ b = b' := by
    apply eq_of_le_of_inf_le_of_le_sup (z := x) hleb'
    · have hxb'b := h b' hb' (le_trans (inf_le_inf_right _ le_sup_left) hleb')
      rwa [le_inf_iff, and_iff_right (inf_le_left.trans hb'le), inf_comm]
    rw [inf_sup_assoc_of_le _ le_sup_left, sup_comm b]
    exact le_inf hb'le (hb'le.trans (sup_le le_sup_left hb₁le))

  simp [RelPerspective, le_antisymm_iff, hleb₁, hb₁le, inf_comm _ x, sup_comm _ x,
    show b ≤ x ⊔ b₁ by simpa using hb'.eq_of_le hb inf_le_right, h b₁ hb₁ hleb₁]

-- lemma Base.frame_of_sup (hb : Base b) (h : ∀ b', Base b' → b' ≤ x ⊔ b → b ≤ x ⊔ b') :
--     Frame b x :=
--   hb.toDual.frame_of_inf h

lemma Frame.relPerspective (h : Frame b x) (hle : x ⊓ b ≤ b') : RelPerspective x b b' := by
  rw [rel]

lemma Frame.inf_eq_inf (h : Frame b x) (hb' : Base b') (hle : x ⊓ b ≤ b') : x ⊓ b' = x ⊓ b := by

  suffices x ⊓ b' ≤ x ⊓ b by simpa [le_antisymm_iff, hle]
  obtain ⟨b₁, hb₁, hleb₁, hb₁le⟩ := exists_base_between_inf_sup hb' h.base (x ⊔ b) x inf_le_left
  obtain ⟨hi, hu⟩ := (frame_iff.1 h).2 _ hb₁ ((le_inf inf_le_sup hle).trans hleb₁) hb₁le
  rw [← hi] at hle ⊢
  rw [← hu] at hleb₁
  exact le_inf inf_le_left <| (inf_le_inf_right _ le_sup_left).trans hleb₁

-- lemma Frame.sup_eq_sup (h : Frame b x) (hb' : Base b') (hle : b' ≤ x ⊔ b) : x ⊔ b' = x ⊔ b :=
--   h.toDual.inf_eq_inf hb' hle

section Indep

/-- An `Indep`endent element is anything below a base. -/
def Indep (i : α) := ∃ b, Base b ∧ i ≤ b

/-- `Basis i x` means that `i` is a maximal independent element below `x`. -/
def Basis (i x : α) := Indep i ∧ i ≤ x ∧ ∀ j, Indep j → i ≤ j → j ≤ x → i = j

lemma Basis.indep (h : Basis i x) : Indep i :=
  h.1

lemma Basis.le (h : Basis i x) : i ≤ x :=
  h.2.1

lemma Basis.eq_of_le (h : Basis i x) (hj : Indep j) (hij : i ≤ j) (hjx : j ≤ x) : i = j :=
  h.2.2 j hj hij hjx

/-- A `Spanning` element is anything above a base. -/
def Spanning (s : α) := ∃ b, Base b ∧ b ≤ s

/-- `Canopy s x` means that `s` is a minimal spanning element above `x`-/
def Canopy (s x : α) := Spanning s ∧ x ≤ s ∧ ∀ t, Spanning t → t ≤ s → x ≤ t → s = t

lemma Indep.mono (hi : Indep i) (hji : j ≤ i) : Indep j :=
  let ⟨b, hb, hib⟩ := hi
  ⟨b, hb, hji.trans hib⟩

lemma Spanning.mono (hs : Spanning s) (hst : s ≤ t) : Spanning t :=
  Indep.mono (α := αᵒᵈ) hs hst

lemma Base.indep (hb : Base b) : Indep b :=
  ⟨b, hb, rfl.le⟩

lemma Base.inf_indep (hb : Base b) : Indep (x ⊓ b) :=
  hb.indep.mono inf_le_right

lemma Base.spanning (hb : Base b) : Spanning b :=
  ⟨b, hb, rfl.le⟩

lemma Indep.exists_base_between_of_spanning (hi : Indep i) (hs : Spanning s) (his : i ≤ s) :
    ∃ b, Base b ∧ i ≤ b ∧ b ≤ s := by
  obtain ⟨b₁, hb₁, hib₁⟩ := hi
  obtain ⟨b₂, hb₂, hb₂s⟩ := hs
  obtain ⟨b, hb, hleb, hble⟩ := exists_base_between_inf_sup hb₁ hb₂ i s
    (inf_le_left.trans (his.trans le_sup_left))
  exact ⟨b, hb, by rwa [← inf_of_le_left hib₁], by rwa [← sup_of_le_left hb₂s]⟩

lemma Indep.exists_le_base_le_sup_base (hi : Indep i) (hb : Base b) :
    ∃ b', Base b' ∧ i ≤ b' ∧ b' ≤ i ⊔ b := by
  obtain ⟨b₁, hb₁, hib₁⟩ := hi
  obtain ⟨b', hb', hleb', hb'le⟩ :=
    exists_base_between_inf_sup hb₁ hb i i (inf_le_left.trans le_sup_left)
  exact ⟨b', hb', by rwa [← inf_of_le_left hib₁], hb'le⟩

lemma base_iff_indep_spanning : Base b ↔ Indep b ∧ Spanning b := by
  refine ⟨fun h ↦ ⟨h.indep, h.spanning⟩, fun ⟨hi, hs⟩ ↦ ?_⟩
  obtain ⟨b', hb', hleb', hb'le⟩ := hi.exists_base_between_of_spanning hs rfl.le
  rwa [← hb'le.antisymm hleb']

lemma Indep.basis_self (hi : Indep i) : Basis i i :=
  ⟨hi, rfl.le, fun _ _ ↦ le_antisymm⟩

-- @[simp] lemma toDual_indep_iff : Indep (toDual s) ↔ Spanning s := Iff.rfl

-- @[simp] lemma toDual_spanning_iff : Spanning (toDual i) ↔ Indep i := Iff.rfl

-- @[simp] lemma toDual_canopy_iff : Canopy (toDual i) (toDual x) ↔ Basis i x := Iff.rfl

-- @[simp] lemma toDual_basis_iff : Basis (toDual s) (toDual x) ↔ Canopy s x := Iff.rfl

lemma Frame.inf_basis (h : Frame b x) : Basis (x ⊓ b) x := by
  refine ⟨h.base.inf_indep, inf_le_left, fun j hj hlej hjle ↦ hlej.antisymm ?_⟩
  obtain ⟨b', hb', hjb', -⟩ := hj.exists_le_base_le_sup_base h.base
  simp [← h.inf_eq_inf hb' (hlej.trans hjb'), hjle, hjb']

lemma Frame.sup_canopy (h : Frame b x) : Canopy (x ⊔ b) x :=
  h.toDual.inf_basis

lemma Base.frame_iff_inf_basis (hb : Base b) : Frame b x ↔ Basis (x ⊓ b) x :=
  ⟨Frame.inf_basis, fun h ↦ hb.frame_of_inf fun b' hb' hleb' ↦ by
    simp [← h.eq_of_le (hb'.inf_indep) (le_inf inf_le_left hleb') inf_le_left]⟩

-- lemma Base.frame_iff_sup_canopy (hb : Base b) : Frame b x ↔ Canopy (x ⊔ b) x :=
--   hb.toDual.frame_iff_inf_basis

lemma Basis.exists_frame_eq_inf (hix : Basis i x) : ∃ b, Frame b x ∧ i = x ⊓ b := by
  obtain ⟨b, hb, hib⟩ := hix.indep
  obtain rfl := hix.eq_of_le (hb.inf_indep) (le_inf hix.le hib) inf_le_left
  rw [← hb.frame_iff_inf_basis] at hix
  exact ⟨b, hix, rfl⟩

lemma Frame.switch_of_inf (h : Frame b x) (hb' : Base b') (hle : x ⊓ b ≤ b') : Frame b' x := by
  rwa [hb'.frame_iff_inf_basis, h.inf_eq_inf hb' hle, ← h.base.frame_iff_inf_basis]

lemma Frame.switch_of_sup (h : Frame b x) (hb' : Base b') (hle : b' ≤ x ⊔ b) : Frame b' x :=
  h.toDual.switch_of_inf hb' hle

lemma exists_basis (x : α) : ∃ i, Basis i x :=
  ⟨_, (exists_frame x).choose_spec.inf_basis⟩

-- lemma exists_canopy (x : α) : ∃ s, Canopy s x :=
--   exists_basis <| toDual x

lemma exists_frame_frame_of_le (hxy : x ≤ y) : ∃ b, Frame b x ∧ Frame b y := by
  obtain ⟨b₁, hb₁⟩ := exists_frame x
  obtain ⟨b₂, hb₂⟩ := exists_frame y
  obtain ⟨b, hb, hleb, hble⟩ := exists_base_between_inf_sup hb₁.base hb₂.base x (x ⊓ b₁) le_sup_left
  refine ⟨b, hb₁.switch_of_inf hb hleb, hb₂.switch_of_sup hb <| hble.trans ?_⟩
  exact sup_le_sup_right (inf_le_left.trans hxy) _

theorem Indep.le_basis_le_sup (hi : Indep i) (hjx : Basis j x) (hix : i ≤ x) :
    ∃ k, Basis k x ∧ i ≤ k ∧ k ≤ i ⊔ j := by
  obtain ⟨b, hb, rfl⟩ := hjx.exists_frame_eq_inf
  obtain ⟨b', hb', hib', hb's⟩ := hi.exists_base_between_of_spanning (s := i ⊔ b)
    (hb.base.spanning.mono le_sup_right) le_sup_left
  refine ⟨x ⊓ b', Frame.inf_basis ?_, le_inf hix hib', ?_⟩
  · exact hb.switch_of_sup hb' <| hb's.trans (sup_le_sup_right hix _)
  rw [sup_comm, inf_sup_assoc_of_le _ hix, sup_comm]
  exact inf_le_inf_left _ hb's

end Indep

section Span

/-- `SpansLE x y` means that `x ≤ y` and every basis for `x` is a basis for `y`. -/
def SpansLE (x y : α) := x ≤ y ∧ ∀ i, Basis i x → Basis i y

def CospansLE (x y : α) := SpansLE (toDual y) (toDual x)
-- x ≤ y ∧ ∀ s, Canopy s y → Canopy s x

@[simp] lemma SpansLE.refl : SpansLE x x := ⟨rfl.le, by simp⟩

@[simp] lemma CospansLE.refl : CospansLE x x := ⟨rfl.le, by simp⟩

-- @[simp] lemma cospansLE_dual_iff : CospansLE (toDual x) (toDual y) ↔ SpansLE y x := Iff.rfl

-- @[simp] lemma spansLE_dual_iff : SpansLE (toDual x) (toDual y) ↔ CospansLE y x := Iff.rfl

theorem spansLE_strongRefinement : StrongRefinement α SpansLE := by
  refine ⟨fun _ _ h ↦ h.1, fun x y z hxy hyz ↦
    ⟨fun ⟨_, h⟩ ↦ ⟨⟨hxy, fun i hi ↦ ?_⟩, ⟨hyz, fun i hi ↦ ?_⟩⟩,
    fun ⟨h,h'⟩ ↦ ⟨hxy.trans hyz, fun i hi ↦ h'.2 _ <| h.2 i hi⟩⟩⟩
  · exact ⟨hi.1, hi.2.1.trans hxy, fun j hj hij hjy ↦ (h i hi).2.2 j hj hij (hjy.trans hyz)⟩
  obtain ⟨j, hj⟩ := exists_basis x
  obtain ⟨k, hk, hik, hkij⟩ := hi.indep.le_basis_le_sup (h _ hj) (hi.le.trans hyz)
  rwa [hi.eq_of_le hk.indep hik (hkij.trans <| sup_le hi.le <| hj.le.trans hxy)]

theorem cospansLE_strongRefinement : StrongRefinement α CospansLE :=
  (spansLE_strongRefinement (α := αᵒᵈ)).strongRefinement_ofDual

lemma Basis.spansLE (h : Basis i x) : SpansLE i x :=
  ⟨h.le, fun j hji ↦ by rwa [hji.eq_of_le h.indep hji.le rfl.le]⟩

lemma Canopy.cospansLE (h : Canopy s x) : CospansLE x s :=
  Basis.spansLE (α := αᵒᵈ) h

theorem exists_rel_base {c d : α} (hcd : c ≤ d) : ∃ x, CospansLE c x ∧ SpansLE x d := by
  obtain ⟨b, hbc, hbd⟩ := exists_frame_frame_of_le hcd
  refine ⟨(d ⊓ b) ⊔ c, ?_, ?_⟩
  · refine cospansLE_strongRefinement.rel_left_of_rel hbc.sup_canopy.cospansLE le_sup_right ?_
    simp [show d ⊓ b ≤ c ⊔ b from inf_le_right.trans le_sup_right]
  exact spansLE_strongRefinement.rel_right_of_rel hbd.inf_basis.spansLE (by simp)
    <| by simp [inf_sup_assoc_of_le _ hcd]

lemma SpansLE.inf_eq_inf_of_frame (hxy : SpansLE x y) (hb : Frame b x) : y ⊓ b = x ⊓ b := by
  simp [← (hxy.2 _ hb.inf_basis).eq_of_le (hb.base.inf_indep)
    (inf_le_inf_right _ hxy.1) inf_le_left]

lemma SpansLE.frame_of_frame (hxy : SpansLE x y) (hb : Frame b x) : Frame b y := by
  rw [hb.base.frame_iff_inf_basis, hxy.inf_eq_inf_of_frame hb]
  exact (hxy.2 _ hb.inf_basis)

lemma CospansLE.sup_eq_sup_of_frame (hxy : CospansLE x y) (hb : Frame b y) : x ⊔ b = y ⊔ b :=
  SpansLE.inf_eq_inf_of_frame (α := αᵒᵈ) hxy hb

lemma CospansLE.frame_of_frame (hxy : CospansLE x y) (hb : Frame b y) : Frame b x :=
    SpansLE.frame_of_frame (α := αᵒᵈ) hxy hb

lemma eq_of_diamond (hix : SpansLE (x ⊓ y) x) (hiy : SpansLE (x ⊓ y) y)
    (hxu : CospansLE x (x ⊔ y)) (hyu : CospansLE y (x ⊔ y)) : x = y := by
  obtain ⟨b, hbi, hbu⟩ := exists_frame_frame_of_le (show x ⊓ y ≤ x ⊔ y from inf_le_sup)
  have hbx := hix.frame_of_frame hbi
  have hby := hiy.frame_of_frame hbi
  apply eq_of_frame_frame hbx hby
  · rw [hix.inf_eq_inf_of_frame hbi, hiy.inf_eq_inf_of_frame hbi]
  rw [hxu.sup_eq_sup_of_frame hbu, hyu.sup_eq_sup_of_frame hbu]

lemma SpansLE.eq_of_cospansLE (h₀ : SpansLE x y) (h₁ : CospansLE x y) : x = y := by
  simpa [inf_of_le_left h₀.1, h₀, sup_of_le_right h₀.1, h₁] using eq_of_diamond (x := x) (y := y)

lemma Indep.cospansLE_of_le (hi : Indep i) (hji : j ≤ i) : CospansLE j i := by
  obtain ⟨b, hbj, hbi⟩ := exists_rel_base hji
  rwa [← (hbi.2 _ (hi.mono hbi.1).basis_self).eq_of_le hi hbi.1 rfl.le]

lemma indep_iff_forall_cospansLE : Indep i ↔ ∀ ⦃j⦄, j ≤ i → CospansLE j i := by
  refine ⟨fun h _ ↦ h.cospansLE_of_le, fun h ↦ ?_⟩
  obtain ⟨b, hb⟩ := exists_basis i
  rw [← hb.spansLE.eq_of_cospansLE (h hb.le)]
  exact hb.indep

lemma Spanning.spansLE_of_le (hs : Spanning s) (hst : s ≤ t) : SpansLE s t :=
  Indep.cospansLE_of_le (α := αᵒᵈ) hs hst

lemma spanning_iff_forall_spansLE : Spanning s ↔ ∀ ⦃t⦄, s ≤ t → SpansLE s t :=
  indep_iff_forall_cospansLE (α := αᵒᵈ)

end Span
section Supermatroid

/-- A `BaseSupermatroid` gives a `Supermatroid`. -/
instance toSupermatroid (α : Type*) [Lattice α] [IsModularLattice α] [BaseSupermatroid α] :
    Supermatroid α where
  SpansLE := SpansLE
  CospansLE := CospansLE
  spansLE_refinement := spansLE_strongRefinement
  cospansLE_refinement := cospansLE_strongRefinement
  exists_rel_base _ _ := exists_rel_base
  eq_of_diamond _ _ := eq_of_diamond
  exists_indep' := ⟨_, fun _ h ↦ exists_base.choose_spec.indep.cospansLE_of_le h.le⟩
  exists_spanning' := ⟨_, fun _ h ↦ exists_base.choose_spec.spanning.spansLE_of_le h.le⟩

-- lemma toSupermatroid_spansLE_iff : x ≤₀ y ↔ SpansLE x y := Iff.rfl
-- lemma toSupermatroid_cospansLE_iff : x ≤₁ y ↔ CospansLE x y := Iff.rfl

@[simp] lemma toSupermatroid_indep_iff : Supermatroid.Indep i ↔ Indep i := by
  simp_rw [indep_iff_forall_cospansLE, Supermatroid.indep_iff_forall_cospansLE]; rfl

@[simp] lemma toSupermatroid_spanning_iff : Supermatroid.Spanning s ↔ Spanning s :=
  toSupermatroid_indep_iff (α := αᵒᵈ)

@[simp] lemma toSupermatroid_base_iff : Supermatroid.Base b ↔ Base b := by
  simp [Supermatroid.base_def, base_iff_indep_spanning]

end Supermatroid

end BaseSupermatroid

/-- A definition of a `Supermatroid` via its independent elements and bases.
We assume the lattice has a maximum element `⊤`; this is needed to make a base exist.
(If we didn't include this assumption, we would get silly examples like where the
lattice comprises all finite sets and everything is independent.) -/
class IndepSupermatroid (α : Type*) [Lattice α] [OrderTop α] where
  /-- An independence predicate -/
  (Indep : α → Prop)

  /-- A basis predicate -/
  (Basis : α → α → Prop)

  /-- `Basis i x` means that `i` is a maximal independent element below `x`. -/
  (basis_iff : ∀ ⦃i x⦄, Basis i x ↔ i ∈ maximals (· ≤ ·) {i | Indep i ∧ i ≤ x})

  /-- There exists an independent element -/
  (exists_indep : ∃ i, Indep i)

  /-- Independence is monotone -/
  (indep_of_le : ∀ ⦃i j⦄, Indep j → i ≤ j → Indep i)

  /-- A nonmaximal independent element augments into its join with a maximal one -/
  (indep_augment : ∀ ⦃i b⦄, Indep i → ¬ Basis i ⊤ → Basis b ⊤ → ∃ j, Indep j ∧ i < j ∧ j ≤ i ⊔ b)

  /-- Every independent element below `x` is below a basis for `x`.  -/
  (exists_le_basis_of_indep_le : ∀ i x, i ≤ x → Indep i → ∃ j, Basis j x ∧ i ≤ j)

  /-- A basis for two elements is a basis for their join. -/
  (basis_sup_of_basis_basis : ∀ ⦃i x y⦄, Basis i x → Basis i y → Basis i (x ⊔ y))

namespace IndepSupermatroid

variable [Lattice α] [IsModularLattice α] [OrderTop α] [IndepSupermatroid α]

lemma Basis.indep (h : Basis i x) : Indep i :=
  (basis_iff.1 h).1.1

lemma Basis.le (h : Basis i x) : i ≤ x :=
  (basis_iff.1 h).1.2

lemma Basis.eq_of_le (h : Basis i x) (hj : Indep j) (hij : i ≤ j) (hjx : j ≤ x) : i = j :=
  hij.antisymm <| (basis_iff.1 h).2 ⟨hj, hjx⟩ hij

lemma Indep.basis_of_forall (hi : Indep i) (hix : i ≤ x)
    (h : ∀ j, Indep j → i ≤ j → j ≤ x → i = j) : Basis i x :=
  basis_iff.2 ⟨⟨hi, hix⟩, fun j ⟨hj, hjx⟩ hij ↦ (h j hj hij hjx).symm.le⟩

lemma Indep.exists_le_basis (hi : Indep i) (hix : i ≤ x) : ∃ j, Basis j x ∧ i ≤ j :=
  exists_le_basis_of_indep_le _ _ hix hi

lemma Indep.mono (hj : Indep j) (hij : i ≤ j) : Indep i :=
  indep_of_le hj hij

lemma exists_basis (x : α) : ∃ i, Basis i x := by
  obtain ⟨j, hj⟩ := exists_indep (α := α)
  obtain ⟨i, hi, -⟩ := (hj.mono <| inf_le_left (b := x)).exists_le_basis inf_le_right
  exact ⟨i, hi⟩

abbrev Base (b : α) := Basis b ⊤

lemma Base.eq_of_le_indep (hb : Base b) (hi : Indep i) (hbi : b ≤ i) : b = i :=
  Basis.eq_of_le hb hi hbi le_top

lemma Base.indep (hb : Base b) : Indep b :=
  Basis.indep hb

lemma Basis.inf_indep (hb : Base b) : Indep (x ⊓ b) :=
  hb.indep.mono inf_le_right

lemma base_antichain : IsAntichain (· ≤ ·) {b : α | Base b} :=
  fun _ hb _ hb' hne hle ↦ hne <| (Base.eq_of_le_indep hb hb'.indep hle)

lemma Indep.exists_le_base (hi : Indep i) : ∃ b, Base b ∧ i ≤ b :=
  hi.exists_le_basis le_top

lemma exists_base : ∃ (b : α), Base b := by
  obtain ⟨i, hi⟩ := exists_indep (α := α)
  obtain ⟨b, hb, -⟩ := hi.exists_le_base
  exact ⟨b, hb⟩

lemma Base.base_of_basis_sup (hb : Base b) (hb' : Basis b' (x ⊔ b)) : Base b' := by
  refine hb'.indep.basis_of_forall le_top fun j hj hb'j _ ↦ by_contra fun hne ↦ ?_
  have hlt := hb'j.lt_of_ne hne
  have hnot : ¬ Basis b' ⊤ := fun hbas ↦ by simp [hbas.eq_of_le hj hlt.le le_top] at hlt
  obtain ⟨k, hk, hltk, hkle⟩ := indep_augment hb'.indep hnot hb
  obtain rfl : b' = k := hb'.eq_of_le hk hltk.le (hkle.trans (sup_le hb'.le le_sup_right))
  exact hltk.ne rfl

lemma exists_base_between_inf_sup (hb₁ : Base b₁) (hb₂ : Base b₂) (x₁ x₂ : α)
    (hle : x₁ ⊓ b₁ ≤ x₂ ⊔ b₂) : ∃ b, Base b ∧ x₁ ⊓ b₁ ≤ b ∧ b ≤ x₂ ⊔ b₂ := by
  have hxb₁ : Indep (x₁ ⊓ b₁) := hb₁.inf_indep
  obtain ⟨b, hb, hleb⟩ := hxb₁.exists_le_basis hle
  exact ⟨b,  hb₂.base_of_basis_sup hb, hleb, hb.le⟩

/-- `Frame b x` means that `b` is a base intersecting `x` in a basis. The hard part is showing
that that is the same definition that a `BaseSupermatroid` requires.  -/
def Frame (b x : α) := Base b ∧ Basis (x ⊓ b) x

lemma frame_iff : Frame b x ↔ Base b ∧ ∀ b₁, Base b₁ → x ⊓ b ≤ b₁ → b₁ ≤ x ⊔ b →
    x ⊓ b₁ = x ⊓ b ∧ x ⊔ b₁ = x ⊔ b := by
  rw [Frame, and_congr_right_iff]
  refine fun hb ↦ ⟨fun h b₁ hb₁ hleb₁ hb₁le ↦ ?_, ?_⟩
  · rw [← h.eq_of_le (hb₁.inf_indep) (le_inf inf_le_left hleb₁) inf_le_left]
    suffices b ≤ x ⊔ b₁ by simpa [le_antisymm_iff, hb₁le]
    obtain ⟨b₂, hb₂', hib₂ : (x ⊔ b₁) ⊓ b ≤ b₂⟩ := hb.inf_indep.exists_le_basis inf_le_left
    have hb₂ : Base b₂ := hb₁.base_of_basis_sup hb₂'
    have h_eq : (x ⊔ b₁) ⊓ b = b₂ := eq_of_le_of_inf_le_of_le_sup hib₂ (z := x) ?_ ?_
    · rw [← hb₂.eq_of_le_indep hb.indep (by simp [← h_eq]), ← h_eq]
      exact inf_le_left
    · rw [inf_comm, ← h.eq_of_le hb₂.inf_indep (le_inf _ (le_trans _ hib₂))] <;>
      simp [inf_le_inf_right b (show x ≤ x ⊔ b₁ from le_sup_left)]
    rw [inf_sup_assoc_of_le _ le_sup_left, sup_comm b]
    refine le_inf ?_ (hb₂'.le.trans ?_) <;> simp [hb₂'.le, hb₁le]

  refine fun h ↦ (hb.inf_indep).basis_of_forall inf_le_left fun j hj hxbj hjx ↦ ?_
  obtain ⟨b', hb', hjb'⟩ := hj.exists_le_basis (hjx.trans (le_sup_left (b := b)))
  rw [le_antisymm_iff, and_iff_right hxbj,
    ← (h b' (hb.base_of_basis_sup hb') (hxbj.trans hjb') hb'.le).1]
  exact le_inf hjx hjb'

lemma exists_frame (x : α) : ∃ b, Frame b x := by
  obtain ⟨i, hi⟩ := exists_basis x
  obtain ⟨b, hb, hib⟩ := hi.indep.exists_le_base
  obtain rfl := hi.eq_of_le (hb.inf_indep) (le_inf hi.le hib) inf_le_left
  exact ⟨b, hb, hi⟩

lemma Frame.eq_of_frame_of_inf_eq_of_sup_eq (hx : Frame b x) (hy : Frame b y) (hi : x ⊓ b = y ⊓ b)
    (hu : x ⊔ b = y ⊔ b) : x = y := by
  have hbu := basis_sup_of_basis_basis hx.2 (hi.symm ▸ hy.2)
  rw [le_antisymm_iff, ← sup_eq_right, ← sup_eq_left, eq_comm, eq_comm (b := x)]
  refine ⟨eq_of_le_of_inf_le_of_sup_le le_sup_right (z := b) (Eq.symm ?_).le ?_,
    eq_of_le_of_inf_le_of_sup_le le_sup_left (z := b) (Eq.symm ?_).le ?_⟩
  · exact (hi ▸ hbu).eq_of_le hx.1.inf_indep (inf_le_inf_right _ le_sup_right) inf_le_left
  · rw [sup_assoc, ← hu, ← sup_assoc, sup_idem]
  · refine hbu.eq_of_le hx.1.inf_indep (inf_le_inf_right _ le_sup_left) inf_le_left
  rw [sup_assoc, ← hu, ← sup_assoc, sup_idem]

/-- An `IndepSupermatroid` determines a `BaseSupermatroid` (and hence a `Supermatroid`). -/
instance toBaseSupermatroid : BaseSupermatroid α where
  Base := Base
  antichain := base_antichain
  exists_base := exists_base
  exists_base_between_inf_sup _ _ := exists_base_between_inf_sup
  Frame := Frame
  frame_iff _ _ := frame_iff
  exists_frame := exists_frame
  eq_of_frame_frame _ _ _ := Frame.eq_of_frame_of_inf_eq_of_sup_eq

@[simp] lemma toBaseSupermatroid_base_iff : BaseSupermatroid.Base b ↔ Base b := Iff.rfl

@[simp] lemma toBaseSupermatroid_frame_iff : BaseSupermatroid.Frame b x ↔ Frame b x := Iff.rfl

@[simp] lemma toBaseSupermatroid_indep_iff : BaseSupermatroid.Indep i ↔ Indep i :=
  ⟨fun ⟨_, hb, hib⟩ ↦ (Base.indep hb).mono hib, Indep.exists_le_base⟩

@[simp] lemma toBaseSupermatroid_basis_iff : BaseSupermatroid.Basis i x ↔ Basis i x := by
  simp only [BaseSupermatroid.Basis, toBaseSupermatroid_indep_iff, basis_iff, mem_maximals_iff]
  aesop
