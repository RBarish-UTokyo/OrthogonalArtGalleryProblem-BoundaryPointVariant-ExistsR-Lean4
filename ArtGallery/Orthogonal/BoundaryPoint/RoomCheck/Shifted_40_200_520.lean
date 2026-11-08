module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomRow.Shifted
public import ArtGallery.Orthogonal.BoundaryPoint.RoomSplit.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.Shifted_40_200_520

/-! Room facts of profile `Shifted_40_200_520` (generated): the corridor spots miss the window wedges of the
critical boxes, the corridor program has certified register boxes, and the catalogue entry. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomCheck.Shifted_40_200_520
open MarginCert RoomWedge RoomGlobal WingOrder.Shifted_40_200_520 ChartDrawing

theorem clear1 : corridorClear template.corridor RoomRow.Shifted.win RoomRow.Shifted.box1 RoomRow.Shifted.xmin=true := by
  decide +kernel
theorem clear2 : corridorClear template.corridor RoomRow.Shifted.win RoomRow.Shifted.box2 RoomRow.Shifted.xmin=true := by decide +kernel

theorem program_ok : ok (params 3) [] (template.corridor.baseRows++template.corridor.rest)=true :=
  WingDoor.Shifted_40_200_520.checks

theorem room_eq : template.room=⟨RoomFamily.Shifted.xAxis,RoomFamily.Shifted.yAxis,RoomFamily.Shifted.cells,
    RoomFamily.Shifted.roles⟩ := rfl

theorem tag_eq : catalog[1]?=some template := rfl

end ArtGallery.Orthogonal.BoundaryPoint.RoomCheck.Shifted_40_200_520
end
