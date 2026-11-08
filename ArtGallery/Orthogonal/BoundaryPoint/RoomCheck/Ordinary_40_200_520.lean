module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomRow.Ordinary
public import ArtGallery.Orthogonal.BoundaryPoint.RoomSplit.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.Ordinary_40_200_520

/-! Room facts of profile `Ordinary_40_200_520` (generated): the corridor spots miss the window wedges of the
critical boxes, the corridor program has certified register boxes, and the catalogue entry. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomCheck.Ordinary_40_200_520
open MarginCert RoomWedge RoomGlobal WingOrder.Ordinary_40_200_520 ChartDrawing

theorem clear1 : corridorClear template.corridor RoomRow.Ordinary.win RoomRow.Ordinary.box1 RoomRow.Ordinary.xmin=true := by
  decide +kernel
theorem clear2 : corridorClear template.corridor RoomRow.Ordinary.win RoomRow.Ordinary.box2 RoomRow.Ordinary.xmin=true := by decide +kernel

theorem program_ok : ok (params 3) [] (template.corridor.baseRows++template.corridor.rest)=true :=
  WingDoor.Ordinary_40_200_520.checks

theorem room_eq : template.room=⟨RoomFamily.Ordinary.xAxis,RoomFamily.Ordinary.yAxis,RoomFamily.Ordinary.cells,
    RoomFamily.Ordinary.roles⟩ := rfl

theorem tag_eq : catalog[0]?=some template := rfl

end ArtGallery.Orthogonal.BoundaryPoint.RoomCheck.Ordinary_40_200_520
end
