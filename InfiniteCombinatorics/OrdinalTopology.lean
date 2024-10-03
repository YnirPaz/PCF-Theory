import Mathlib
import InfiniteCombinatorics.OrdinalArithmetic

universe u

namespace Ordinal

open Set Order

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

theorem IsAcc.inter_Ioo_nonempty {o : Ordinal} {S : Set Ordinal} (hS : o.IsAcc S)
    {p : Ordinal} (hp : p < o) : (S ∩ Ioo p o).Nonempty := hS.2 p hp

theorem isClosed_zero (S : Set Ordinal) : IsClosed S 0 := fun _ h ↦
  False.elim <| (Ordinal.zero_le _).not_lt h

theorem IsClosed.sInter {o : Ordinal} {S : Set (Set Ordinal)} (h : ∀ C ∈ S, IsClosed C o) :
    IsClosed (⋂₀ S) o :=
  fun p plto pAcc C CmemS ↦ (h C CmemS) p plto (pAcc.subset (sInter_subset_of_mem CmemS))

theorem IsClosed.iInter {ι : Type u} {f : ι → Set Ordinal} {o : Ordinal}
    (h : ∀ i, IsClosed (f i) o) : IsClosed (⋂ i, f i) o :=
  IsClosed.sInter fun _ ⟨i, hi⟩ ↦ hi ▸ (h i)

end Ordinal
