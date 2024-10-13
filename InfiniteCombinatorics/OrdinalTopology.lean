import Mathlib
import InfiniteCombinatorics.OrdinalArithmetic
import InfiniteCombinatorics.OrdinalBasic

universe u v

open Set Order

namespace Ordinal

-- Small.{u} → Small.{max u v} isn't properly synthed, so this instance is required.
instance {o : Ordinal.{u}} : Small.{max u v} (Iio o) := small_lift (Iio o)


-- #16710

def IsAcc (o : Ordinal) (S : Set Ordinal) : Prop :=
  o ≠ 0 ∧ ∀ p < o, (S ∩ Ioo p o).Nonempty

def IsClosed (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ p < o, IsAcc p S → p ∈ S

theorem IsAcc.subset {o : Ordinal} {S T : Set Ordinal} (h : S ⊆ T) (ho : o.IsAcc S) :
    o.IsAcc T := ⟨ho.1, fun p plto ↦ (ho.2 p plto).casesOn fun s hs ↦ ⟨s, h hs.1, hs.2⟩⟩

theorem IsAcc.isLimit {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S) : IsLimit o := by
  refine isLimit_of_not_succ_of_ne_zero (fun ⟨x, hx⟩ ↦ ?_) h.1
  rcases h.2 x (lt_of_lt_of_le (lt_succ x) hx.symm.le) with ⟨p, hp⟩
  exact (hx.symm ▸ (succ_le_iff.mpr hp.2.1)).not_lt hp.2.2

theorem IsAcc.inter_Ioo_nonempty {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S)
    {p : Ordinal} (hp : p < o) : (S ∩ Ioo p o).Nonempty := h.2 p hp

-- not contributed
theorem IsAcc.inter_Ioi {o p : Ordinal} {S : Set Ordinal} (hp : p < o) (h : o.IsAcc S) :
    o.IsAcc (S ∩ Ioi p) := by
  use h.1
  intro q qlt
  obtain ⟨x, hx⟩ := h.2 (max p q) (max_lt hp qlt)
  use x
  refine ⟨⟨hx.1, (max_lt_iff.mp hx.2.1).1⟩, (max_lt_iff.mp hx.2.1).2, hx.2.2⟩

-- not contributed
theorem IsClosed.mem_of_isAcc {o p : Ordinal} {S : Set Ordinal} (h : o.IsClosed S) :
    p < o → p.IsAcc S → p ∈ S := fun plt hp ↦ h p plt hp

theorem isClosed_zero (S : Set Ordinal) : IsClosed S 0 := fun _ h ↦
  False.elim <| (Ordinal.zero_le _).not_lt h

theorem IsClosed.sInter {o : Ordinal} {S : Set (Set Ordinal)} (h : ∀ C ∈ S, IsClosed C o) :
    IsClosed (⋂₀ S) o :=
  fun p plto pAcc C CmemS ↦ (h C CmemS) p plto (pAcc.subset (sInter_subset_of_mem CmemS))

theorem IsClosed.iInter {ι : Type u} {f : ι → Set Ordinal} {o : Ordinal}
    (h : ∀ i, IsClosed (f i) o) : IsClosed (⋂ i, f i) o :=
  IsClosed.sInter fun _ ⟨i, hi⟩ ↦ hi ▸ (h i)

-- not contributed
theorem blahblah {o : Ordinal.{u}} {f : Iio o → Ordinal.{max u v}} {S : Set Ordinal} (ho : o.IsLimit)
    (hf : StrictMono f) (h : ∃ r, ∀ t, r < t → f t ∈ S) : (⨆ i, f i).IsAcc S := by
  constructor
  · rw [← Ordinal.pos_iff_ne_zero, Ordinal.lt_iSup']
    use ⟨1, ho.one_lt⟩
    have : f ⟨0, ho.pos⟩ < f ⟨1, ho.one_lt⟩ := hf (Subtype.mk_lt_mk.mpr zero_lt_one)
    exact Ordinal.pos_of_gt this
  · intro p plt
    rw [Ordinal.lt_iSup'] at plt
    obtain ⟨q, hq⟩ := plt
    obtain ⟨r, hr⟩ := h
    have lto : max r.1 q.1 + 1 < o := sorry
    specialize hr ⟨max r.1 q.1 + 1, lto⟩ sorry
    use f ⟨max r.1 q.1 + 1, lto⟩
    refine ⟨hr, ⟨?_, ?_⟩⟩
    · sorry
    · rw [Ordinal.lt_iSup']
      use ⟨max r.1 q.1 + 2, sorry⟩
      apply hf
      rw [Subtype.mk_lt_mk]
      sorry



end Ordinal
