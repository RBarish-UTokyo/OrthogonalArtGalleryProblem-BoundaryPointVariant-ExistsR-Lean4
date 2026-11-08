module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomRow.Lower
public import ArtGallery.Orthogonal.BoundaryPoint.RoomSplit.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.Lower_10_40_1000

/-! Room facts of profile `Lower_10_40_1000` (generated): the corridor spots miss the window wedges of the
critical boxes, the corridor program has certified register boxes, and the catalogue entry. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomCheck.Lower_10_40_1000
open MarginCert RoomWedge RoomGlobal WingOrder.Lower_10_40_1000 ChartDrawing

theorem clear1 : corridorClear template.corridor RoomRow.Lower.win RoomRow.Lower.box1 RoomRow.Lower.xmin=true := by
  decide +kernel
theorem clear2 : corridorClear template.corridor RoomRow.Lower.win RoomRow.Lower.box2 RoomRow.Lower.xmin=true := by decide +kernel

theorem program_ok : ok (params 3) [] (template.corridor.baseRows++template.corridor.rest)=true :=
  WingDoor.Lower_10_40_1000.checks

theorem room_eq : template.room=⟨RoomFamily.Lower.xAxis,RoomFamily.Lower.yAxis,RoomFamily.Lower.cells,
    RoomFamily.Lower.roles⟩ := rfl

theorem tag_eq : catalog[3]?=some template := rfl

end ArtGallery.Orthogonal.BoundaryPoint.RoomCheck.Lower_10_40_1000
end
