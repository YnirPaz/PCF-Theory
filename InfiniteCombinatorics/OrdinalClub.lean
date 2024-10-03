import Mathlib
import InfiniteCombinatorics.OrdinalTopology
import InfiniteCombinatorics.OrdinalArithmetic
import InfiniteCombinatorics.OrdinalBasic
import InfiniteCombinatorics.CardinalCofinality

noncomputable section

universe u v

open Classical Cardinal Set Order Filter

namespace Ordinal

-- Small.{u} → Small.{max u v} isn't properly synthed, so this instance is required.
instance {o : Ordinal.{u}} : Small.{max u v} (Iio o) := small_lift (Iio o)

/-- A set of ordinals is a club below an ordinal if it is closed and unbounded in it. -/
def IsClub (C : Set Ordinal) (o : Ordinal) : Prop :=
  IsClosed C o ∧ IsAcc o C

theorem IsClub.inter_Iio {o : Ordinal} {C : Set Ordinal} (h : o.IsClub C) : -- ugly proof
    o.IsClub (C ∩ (Iio o)) := by
  constructor
  · exact fun p plt hp ↦ ⟨h.1 p plt (hp.subset inter_subset_left), plt⟩
  · exact ⟨h.2.1, fun p plt ↦ (h.2.2 p plt).casesOn fun x hx ↦
      ⟨x, ⟨⟨hx.1, hx.2.2⟩, hx.2.1, hx.2.2⟩⟩⟩


section ClubIntersection

variable {o : Ordinal.{u}} {S : Set (Set Ordinal)}
variable {ι : Type u} {f : ι → Set Ordinal}

theorem exists_above_of_lt_cof {p : Ordinal} (h : p < o) (hS : Nonempty S)
    (hSacc : ∀ s ∈ S, o.IsAcc s) (hScard : #S < Cardinal.lift.{u + 1, u} o.cof) :
    ∃ q < o, p < q ∧ ∀ U ∈ S, (U ∩ Ioo p q).Nonempty := by
  haveI : Small.{u, u + 1} S := by
    rw [small_iff_lift_mk_lt_univ, Cardinal.lift_id]
    exact hScard.trans <| lift_lt_univ o.cof
  obtain ⟨s, hs⟩ := hS
  have infMem := csInf_mem <| (hSacc s hs).inter_Ioo_nonempty h
  let f : S → Ordinal := fun s ↦ sInf (s ∩ (Ioo p o))
  use iSup f + 1
  refine ⟨?_, ?_, ?_⟩
  · apply (hSacc s hs).isLimit.succ_lt
    apply Ordinal.iSup_lt_ord'
    convert hScard
    · exact Cardinal.lift_id'.{u, u + 1} #S
    · intro s
      have := csInf_mem <| (hSacc s.1 s.2).inter_Ioo_nonempty h
      exact this.2.2
  · refine lt_trans ?_ (lt_succ _)
    rw [Ordinal.lt_iSup']
    use ⟨s, hs⟩
    exact infMem.2.1
  · intro s hs
    use sInf (s ∩ (Ioo p o))
    constructor
    · refine mem_of_mem_inter_left (csInf_mem ?_)
      exact (hSacc s hs).inter_Ioo_nonempty h
    · constructor
      · have := csInf_mem <| (hSacc s hs).inter_Ioo_nonempty h
        exact this.2.1
      · refine lt_of_le_of_lt ?_ (lt_succ _)
        exact Ordinal.le_iSup' f ⟨s, hs⟩

theorem exists_omega_seq_succ_prop (opos : 0 < o) {P : Ordinal.{u} → Ordinal.{u} → Prop}
    (hP : ∀ p : Iio o, ∃ q, (p < q ∧ P p q)) (r : Iio o) : ∃ f : (Iio ω) → Iio o,
    (∀ i, P (f i) (f ⟨succ i, omega_isLimit.2 i i.2⟩)) ∧ StrictMono f
    ∧ r < f ⟨0, omega_pos⟩ := by
  have oLim : o.IsLimit := ⟨opos.ne.symm, fun a alto ↦ (hP ⟨a, alto⟩).casesOn fun r hr ↦
  lt_of_le_of_lt (succ_le_of_lt hr.1) r.2⟩
  let H₂ : (p : Iio ω) → (Iio o) → (Iio o) := fun _ fp ↦ choose (hP fp)
  let H₃ : (w : Iio ω) → IsLimit w → ((o' : Iio ω) → o' < w → (Iio o)) → (Iio o) :=
    fun w _ _ ↦ ⟨0, oLim.pos⟩
  let f : Iio ω → Iio o := fun n ↦ @boundedLimitRecOn ω omega_isLimit (fun _ ↦ Iio o) n
    ⟨r + 1, oLim.succ_lt r.2⟩ H₂ H₃
  use f
  constructor <;> try constructor
  · intro n
    simp [f, H₂]
    generalize_proofs _ pf
    exact (choose_spec pf).2
  · have aux : ∀ i, f i < f ⟨i + 1, omega_isLimit.2 i i.2⟩ := fun i ↦ by
      simp [f, H₂]
      generalize_proofs _ pf
      exact (choose_spec pf).casesOn fun h _ ↦ h
    exact strictMono_of_succ_lt_omega f aux
  simp [f]
  exact lt_succ r.1

theorem exists_omega_seq_succ_prop_pos (opos : 1 < o) {P : Ordinal.{u} → Ordinal.{u} → Prop}
    (hP : ∀ p : Iio o, 0 < p.1 → ∃ q, (p < q ∧ P p q)) (r : Iio o) : ∃ f : (Iio ω) → Iio o,
    (∀ i, P (f i) (f ⟨succ i, omega_isLimit.2 i i.2⟩)) ∧ StrictMono f
    ∧ r < f ⟨0, omega_pos⟩ := by
  let P' : Ordinal.{u} → Ordinal → Prop := fun p q ↦ p = 0 ∨ P p q
  have auxP' : ∀ p : Iio o, ∃ q, (p < q ∧ P' p q) := by
    intro p
    by_cases h : p.1 = 0
    · exact ⟨⟨1, opos⟩, (h ▸ (lt_one_iff_zero.mpr rfl) : p.1 < 1), Or.inl h⟩
    obtain ⟨q, hq⟩ := hP p (Ordinal.pos_iff_ne_zero.mpr h)
    exact ⟨q, hq.1, Or.inr hq.2⟩
  obtain ⟨s, hs⟩ := exists_omega_seq_succ_prop (zero_lt_one.trans opos) auxP' r
  use s
  refine ⟨fun i ↦ (hs.1 i).resolve_left ?_, hs.2⟩
  by_cases h : i.1 = 0
  · have := (Ordinal.pos_of_gt (hs.2.2)).ne.symm
    simp_rw [← h] at this
    exact this
  · refine (Ordinal.pos_of_gt (hs.2.1 (?_ : ⟨0, omega_pos⟩ < i))).ne.symm
    exact Ordinal.pos_iff_ne_zero.mpr h

/-- If between every 2 consecutive elements of a weakly increasing `δ`-sequence
  there is an element of `C`, and `δ` is a limit ordinal,
  then the supremum of the sequence is an accumulation point of `C`. -/
theorem isAcc_iSup_of_between {δ : Ordinal.{u}} (C : Set Ordinal) (δLim : δ.IsLimit)
    (s : Iio δ → Ordinal.{max u v}) (sInc : ∀ o, s o < s ⟨succ o, δLim.succ_lt o.2⟩)
    (h : ∀ o, (C ∩ (Ioo (s o) (s ⟨succ o, δLim.succ_lt o.2⟩))).Nonempty) :
    IsAcc (iSup s) C := by
  constructor
  · rw [← Ordinal.pos_iff_ne_zero, Ordinal.lt_iSup']
    use ⟨1, δLim.one_lt⟩
    refine lt_of_le_of_lt (Ordinal.zero_le (s ⟨0, δLim.pos⟩)) ?_
    convert sInc ⟨0, δLim.pos⟩
    exact succ_zero.symm
  intro p hp
  rw [Ordinal.lt_iSup'] at hp
  obtain ⟨r, hr⟩ := hp
  obtain ⟨q, hq⟩ := h r
  use q
  refine ⟨hq.1, ⟨hr.trans hq.2.1, ?_⟩⟩
  rw [Ordinal.lt_iSup']
  exact ⟨⟨r.1 + 1, δLim.succ_lt r.2⟩, hq.2.2⟩

theorem IsClub.sInter (hCof : ℵ₀ < o.cof) (hS : ∀ C ∈ S, IsClub C o) (hSemp : S.Nonempty)
    (Scard : #S < Cardinal.lift.{u + 1, u} o.cof) : IsClub (⋂₀ S) o := by
  refine ⟨IsClosed.sInter (fun C CmemS ↦ (hS C CmemS).1), ?_⟩
  have nonemptyS : Nonempty S := hSemp.to_subtype
  have oLim : IsLimit o := aleph0_le_cof.mp hCof.le
  use oLim.pos.ne.symm
  intro p plto
  let P : Ordinal → Ordinal → Prop := fun p q ↦ ∀ C ∈ S, (C ∩ Ioo p q).Nonempty
  have auxP : ∀ p : Iio o, ∃ q, p < q ∧ P p q := fun p ↦ by
    rcases exists_above_of_lt_cof p.2 nonemptyS (fun U hU ↦ (hS U hU).2) Scard with ⟨q, hq⟩
    use ⟨q, hq.1⟩, hq.2.1, hq.2.2
  rcases exists_omega_seq_succ_prop.{u, u} oLim.pos auxP ⟨p, plto⟩ with ⟨f, hf⟩
  -- SupSet (Iio o)?
  let sup := iSup (fun n ↦ (f n).1)
  use sup
  have suplt : sup < o := by
    apply iSup_lt_ord'
    · change Cardinal.lift #{p | p < ω} < _
      rw [mk_initialSeg, card_omega, lift_aleph0, lift_aleph0]
      exact aleph0_lt_lift.mpr hCof
    intro n
    exact (f n).2
  constructor
  · intro s hs
    apply (hS s hs).1 sup suplt
    apply isAcc_iSup_of_between
    · intro n
      exact hf.2.1 (lt_succ n.1)
    · intro n
      exact hf.1 n s hs
    · exact omega_isLimit
  · constructor
    · rw [Ordinal.lt_iSup']
      exact ⟨⟨0, omega_pos⟩, hf.2.2⟩
    · exact suplt

theorem IsClub.iInter_lift {ι : Type v} {f : ι → Set Ordinal.{u}} [Nonempty ι] (hCof : ℵ₀ < o.cof)
    (hf : ∀ i, IsClub (f i) o)
    (ιCard : Cardinal.lift.{u} #ι < Cardinal.lift.{v} o.cof) : IsClub (⋂ i, f i) o := by
  refine IsClub.sInter (S := range f) hCof (fun y ⟨x, hx⟩ ↦ hx ▸ hf x) (range_nonempty f) ?_
  have := mk_range_le_lift (f := f)
  rw [← Cardinal.lift_lt.{_, max v (u + 1)}]
  have aux : Cardinal.lift.{max v (u + 1), u + 1} #↑(range f) =
      Cardinal.lift.{max v, u + 1} #↑(range f) := by
    convert (@lift_umax_eq.{u + 1, u + 1, v} #(range f) #(range f)).mpr rfl
    exact Cardinal.lift_umax.symm
  rw [aux]
  apply this.trans_lt
  convert lift_strictMono.{max u v, max (u + 1) v} ιCard
  · rw [Cardinal.lift_lift, Cardinal.lift_umax.{v, u + 1}]
  · rw [Cardinal.lift_lift, Cardinal.lift_lift]



-- TODO: review, old code
theorem IsClub.iInter [Nonempty ι] (hCof : ℵ₀ < o.cof) (hf : ∀ i, IsClub (f i) o) -- prove with lift!
    (ιCard : #ι < o.cof) : IsClub (⋂ i, f i) o := by
  let f' : ULift.{u + 1, u} ι → Set Ordinal.{u} := fun ⟨i⟩ ↦ f i
  have rangelt : #(range f') < Cardinal.lift.{u + 1, u} o.cof :=
    lt_of_le_of_lt (@mk_range_le _ _ f') ((mk_uLift _) ▸ (Cardinal.lift_lt.mpr ιCard))
  have clubRange : ∀ C ∈ (range f'), IsClub C o := fun C ⟨⟨i⟩, hi⟩ ↦ hi ▸ hf i
  have intClub := IsClub.sInter hCof clubRange (range_nonempty f') rangelt
  rw [sInter_range] at intClub
  convert intClub
  have : range f = range f' :=
    Set.ext fun x ↦ ⟨fun ⟨i, hi⟩ ↦ ⟨⟨i⟩, hi⟩, fun ⟨⟨i⟩, hi⟩ ↦ ⟨i, hi⟩⟩
  unfold iInter iInf; rw [this]

end ClubIntersection

/-- TODO: write me! -/
def diagInter {o : Ordinal} (c : Iio o → Set Ordinal) : Set Ordinal :=
  {p | ∀ r : Iio o, r < p → p ∈ c r}

prefix:110 "Δ " => diagInter

theorem mem_diagInter {o x : Ordinal} {c : Iio o → Set Ordinal} :
    x ∈ Δ c ↔ ∀ r : Iio o, r < x → x ∈ c r := Iff.rfl

theorem diagInter_Ioi_subset {o : Ordinal} (r : Iio o) (c : Iio o → Set Ordinal) :
    Δ c ∩ Ioi r.1 ⊆ c r :=
  fun _ h ↦ h.1 r h.2

section DiagonalIntersection

theorem isClosed_diagInter {o : Ordinal} {c : Iio o → Set Ordinal} (h : ∀ r, o.IsClosed (c r)) :
    o.IsClosed (Δ c) := by
  intro p plt hp r rlt
  apply (h r).mem_of_isAcc plt
  apply IsAcc.subset (diagInter_Ioi_subset r c)
  exact hp.inter_Ioi rlt

theorem isAcc_diagInter {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hreg : κ.IsRegular)
    {c : Iio κ.ord → Set Ordinal} (hc : ∀ r, IsClub (c r) κ.ord) : IsAcc κ.ord (Δ c) := by
  refine ⟨(ord_zero ▸ ord_strictMono (aleph0_pos.trans hκ)).ne.symm, ?_⟩
  let P : Ordinal.{u} → Ordinal → Prop := fun p q ↦ ∀ r : Iio κ.ord, r.1 < q → q ∈ c r
  have auxP : ∀ r : Iio κ.ord, 0 < r.1 → ∃ s, (r < s ∧ P r s) := by
    intro r hr
    haveI : (Iio r.1).Nonempty := sorry
    let C : Set Ordinal := ⋂ s : Iio r.1, c ⟨s.1, have : s.1 < r.1 := s.2
      this.trans (r.2 : r.1 < κ.ord)⟩
    have : IsClub C κ.ord := by
      dsimp [C]
      have := @IsClub.iInter κ.ord (Iio r.1)

  sorry

end DiagonalIntersection


/-- A set of ordinals is stationary below an ordinal if it intersects every club of it. -/
def IsStationary (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ C, IsClub C o → (S ∩ C).Nonempty

theorem IsStationary.inter_club_below {o : Ordinal} {S C : Set Ordinal} (hS : o.IsStationary S)
    (hC : o.IsClub C) : (S ∩ C ∩ (Iio o)).Nonempty :=
  (inter_assoc _ _ _) ▸ (hS _ hC.inter_Iio)
