import Init.Data.List.Basic
namespace NineGap

def cutGapSlots (l u : Nat) : List Nat := (List.range (u-l)).map (l+·)

theorem centralGapCover :
    (cutGapSlots 158 306 ++ cutGapSlots 207 355).eraseDups =
      cutGapSlots 158 355 := by decide +kernel

theorem shiftedBlockReflection :
    ((cutGapSlots 306 320).map (512-·)).reverse = cutGapSlots 193 207 := by rfl

theorem separateWindows :
    (cutGapSlots 158 172 ++ cutGapSlots 193 207).Nodup := by decide +kernel

theorem bothWindowsInSmallerInterval :
    (cutGapSlots 158 172 ++ cutGapSlots 193 207).all
      (fun r => 158 ≤ r && r < 306) = true := by rfl

#print axioms centralGapCover
#print axioms shiftedBlockReflection
#print axioms separateWindows
#print axioms bothWindowsInSmallerInterval
end NineGap
