module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange
public import ArtGallery.Orthogonal.BoundaryPoint.RegChain
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.InvLe_1_200
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0XDefs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0S0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0S1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0S2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0S3
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0S4
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0S5
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0S6
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0XS0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0XS1

/-! Range data of profile `InvLe_1_200`: `C0XHold` (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200
open MarginCert RegisterTable RegisterOrder KronCert IndexedWing ShapeRefs RoomCoordinates CopyChannel CopyMatch CopyRange
open WingOrder.InvLe_1_200
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

-- @@HOLD c0

noncomputable def c0xtops : List (Nat × Ex × Ex) := [c0f830,c0f684,c0f580,c0f578,c0f575,c0f351,c0f315,c0f309,c0f93]

/-- Closed forms of the registers of the other test of channel 0, step by step. -/
theorem c0xhold {args xs : List ℚ} (m : Model args xs rows boxes cache) {x y z : ℝ}
    (hin : ∀ k Q d, (k,Q,d)∈c0ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev x y z Q)
    (B : PolyBox.Box (1/65:ℚ) (4/5005:ℚ) (509/130130:ℚ) x y z) :
    ∀ t∈c0xtops, RegCert.Holds xs x y z t.1 t.2.1 t.2.2 := by
  have h861 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k861
  have h860 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k860
  have h859 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k859
  have h857 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f861]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k857
  have h856 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k856
  have h855 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f856]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k855
  have h854 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f857,c0f855]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k854
  have h851 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k851
  have h850 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f851]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k850
  have h849 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f854,c0f850]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k849
  have h848 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k848
  have h847 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f849,c0f848]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k847
  have h842 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k842
  have h840 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k840
  have h839 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f859,c0f840]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k839
  have h838 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k838
  have h837 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f839,c0f838]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k837
  have h836 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k836
  have h835 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f861,c0f836]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k835
  have h834 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f860,c0f835]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k834
  have h833 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f837,c0f834]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k833
  have h832 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k832
  have h831 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f832]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k831
  have h830 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f861,c0f831]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k830
  have h829 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k829
  have h828 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f861,c0f829]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k828
  have h827 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f830]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k827
  have h826 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k826
  have h825 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f827,c0f826]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k825
  have h824 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f833]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k824
  have h823 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f847,c0f824]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k823
  have h822 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f823]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k822
  have h821 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f825,c0f822]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k821
  have h820 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f833,c0f821]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k820
  have h819 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f820]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k819
  have h818 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f830,c0f819]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k818
  have h817 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k817
  have h816 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f830,c0f817]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k816
  have h815 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f854,c0f830]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k815
  have h814 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f833,c0f815]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k814
  have h813 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f854,c0f816]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k813
  have h812 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k812
  have h811 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f813,c0f812]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k811
  have h810 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f811]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k810
  have h809 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f814,c0f810]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k809
  have h808 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f817,c0f809]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k808
  have h807 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k807
  have h806 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f808,c0f807]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k806
  have h805 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f854,c0f821]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k805
  have h804 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f833,c0f817]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k804
  have h803 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f804]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k803
  have h802 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f812,c0f803]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k802
  have h801 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f805,c0f802]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k801
  have h800 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f810,c0f801]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k800
  have h799 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f800]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k799
  have h798 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f806,c0f799]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k798
  have h797 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k797
  have h796 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f828,c0f797]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k796
  have h795 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f821,c0f796]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k795
  have h792 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f798,c0f795]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k792
  have h791 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f850,c0f792]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k791
  have h790 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k790
  have h789 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f854,c0f790]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k789
  have h788 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f847,c0f789]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k788
  have h787 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k787
  have h786 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f788,c0f787]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k786
  have h785 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k785
  have h784 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f830,c0f785]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k784
  have h783 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f786,c0f784]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k783
  have h782 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f830,c0f812]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k782
  have h781 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f787,c0f782]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k781
  have h780 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f781]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k780
  have h779 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f783,c0f780]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k779
  have h778 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f812,c0f779]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k778
  have h777 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k777
  have h776 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f778,c0f777]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k776
  have h775 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k775
  have h774 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f828,c0f775]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k774
  have h773 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f785,c0f774]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k773
  have h772 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f847,c0f812]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k772
  have h771 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f772]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k771
  have h770 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f773,c0f771]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k770
  have h769 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f821,c0f770]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k769
  have h768 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f780,c0f769]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k768
  have h767 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f768]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k767
  have h766 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f776,c0f767]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k766
  have h765 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f791]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k765
  have h764 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f847]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k764
  have h763 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f765,c0f764]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k763
  have h762 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f766,c0f765]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k762
  have h761 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f779]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k761
  have h760 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f762,c0f761]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k760
  have h757 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k757
  have h756 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f760,c0f757]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k756
  have h755 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f763,c0f756]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k755
  have h754 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f850,c0f755]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k754
  have h753 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f833,c0f789]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k753
  have h752 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f754,c0f753]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k752
  have h751 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f752]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k751
  have h750 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f795,c0f751]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k750
  have h749 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f765,c0f750]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k749
  have h748 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f850,c0f749]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k748
  have h747 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f854,c0f787]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k747
  have h746 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f847,c0f821]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k746
  have h745 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f823,c0f787]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k745
  have h744 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f746,c0f745]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k744
  have h743 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f833,c0f747]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k743
  have h742 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f821,c0f743]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k742
  have h741 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f742]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k741
  have h740 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f744,c0f741]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k740
  have h739 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f747]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k739
  have h738 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f812,c0f739]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k738
  have h737 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f738]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k737
  have h736 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f740,c0f737]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k736
  have h735 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f830,c0f791]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k735
  have h734 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f735]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k734
  have h733 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f736,c0f734]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k733
  have h728 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f830,c0f754]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k728
  have h727 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f821,c0f728]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k727
  have h726 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f733]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k726
  have h725 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f727,c0f726]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k725
  have h724 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f791,c0f748]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k724
  have h723 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f748,c0f725]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k723
  have h722 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f723]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k722
  have h721 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f754,c0f722]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k721
  have h720 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f833,c0f754]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k720
  have h719 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f791,c0f720]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k719
  have h718 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f815,c0f719]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k718
  have h717 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f854,c0f727]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k717
  have h716 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f812,c0f717]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k716
  have h715 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f716]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k715
  have h714 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f718,c0f715]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k714
  have h713 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f714]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k713
  have h712 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f833,c0f713]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k712
  have h711 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f847,c0f721]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k711
  have h710 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f724,c0f711]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k710
  have h709 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f827,c0f710]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k709
  have h708 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f821,c0f787]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k708
  have h707 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f830,c0f721]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k707
  have h706 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f708,c0f707]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k706
  have h705 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f706]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k705
  have h704 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f709,c0f705]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k704
  have h703 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f847,c0f704]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k703
  have h702 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f821,c0f747]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k702
  have h701 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f787,c0f702]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k701
  have h700 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f823,c0f701]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k700
  have h699 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f737,c0f700]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k699
  have h698 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f847,c0f754]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k698
  have h697 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f791,c0f698]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k697
  have h696 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f830,c0f697]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k696
  have h695 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f696]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k695
  have h694 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f699,c0f695]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k694
  have h693 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f727,c0f704]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k693
  have h692 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f693]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k692
  have h691 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f694,c0f692]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k691
  have h690 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f726,c0f691]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k690
  have h689 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f748,c0f690]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k689
  have h688 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f712]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k688
  have h687 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f703,c0f688]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k687
  have h686 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f687]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k686
  have h685 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f689,c0f686]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k685
  have h684 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k684
  have h683 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f854,c0f684]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k683
  have h682 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f715,c0f683]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k682
  have h681 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f705,c0f683]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k681
  have h680 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f703,c0f681]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k680
  have h676 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f690,c0f682]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k676
  have h675 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f725,c0f712]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k675
  have h674 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f675]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k674
  have h673 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f812,c0f674]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k673
  have h672 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f681,c0f673]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k672
  have h671 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f672]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k671
  have h670 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f676,c0f671]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k670
  have h669 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f748,c0f670]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k669
  have h668 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f688,c0f680]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k668
  have h667 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f682]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k667
  have h666 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f668,c0f667]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k666
  have h665 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f687,c0f666]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k665
  have h664 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f665]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k664
  have h663 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f669,c0f664]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k663
  have h661 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f854,c0f775]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k661
  have h660 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f705,c0f661]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k660
  have h659 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f703,c0f660]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k659
  have h657 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f673,c0f660]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k657
  have h656 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f657]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k656
  have h655 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f676,c0f656]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k655
  have h654 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f748,c0f655]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k654
  have h653 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f688,c0f659]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k653
  have h652 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f667,c0f653]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k652
  have h651 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f687,c0f652]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k651
  have h650 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f651]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k650
  have h649 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f654,c0f650]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k649
  have h647 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f789,c0f715]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k647
  have h643 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f690,c0f647]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k643
  have h642 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f671,c0f643]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k642
  have h641 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f748,c0f642]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k641
  have h640 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f647]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k640
  have h639 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f668,c0f640]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k639
  have h638 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f687,c0f639]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k638
  have h637 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f638]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k637
  have h636 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f641,c0f637]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k636
  have h633 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f656,c0f643]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k633
  have h632 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f748,c0f633]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k632
  have h631 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f653,c0f640]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k631
  have h630 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f687,c0f631]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k630
  have h629 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f630]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k629
  have h628 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f632,c0f629]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k628
  have h626 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f663]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k626
  have h625 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f649]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k625
  have h624 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f636]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k624
  have h623 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f628]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k623
  have h622 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f626,c0f625]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k622
  have h621 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f624,c0f622]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k621
  have h620 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f623,c0f621]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k620
  have h619 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f620]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k619
  have h617 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k617
  have h616 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f847,c0f617]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k616
  have h615 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f616]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k615
  have h614 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f851,c0f615]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k614
  have h580 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f818,c0f735]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k580
  have h579 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f821,c0f812]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k579
  have h578 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f707,c0f579]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k578
  have h577 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f754,c0f685]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k577
  have h576 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f830,c0f577]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k576
  have h575 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f579,c0f576]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k575
  have h351 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f728,c0f579]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k351
  have h343 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k343
  have h342 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f343]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k342
  have h341 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f854,c0f342]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k341
  have h338 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k338
  have h337 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f338]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k337
  have h336 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f830,c0f337]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k336
  have h316 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f830,c0f724]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k316
  have h315 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f818,c0f316]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k315
  have h314 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f685,c0f614]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k314
  have h313 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f619,c0f314]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k313
  have h312 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f850,c0f313]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k312
  have h311 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f754,c0f312]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k311
  have h310 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f830,c0f311]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k310
  have h309 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f579,c0f310]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k309
  have h127 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f342,c0f336]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k127
  have h126 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f127]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k126
  have h125 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k125
  have h124 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f126,c0f125]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k124
  have h123 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f124]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k123
  have h112 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f842]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k112
  have h111 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f336,c0f112]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k111
  have h110 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f111]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k110
  have h109 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f580,c0f110]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k109
  have h106 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f123,c0f109]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k106
  have h99 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f109]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k99
  have h95 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f106,c0f99]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k95
  have h94 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f341,c0f95]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k94
  have h93 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f109,c0f94]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k93
  intro t ht
  simp only [c0xtops,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> assumption

end ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200
end
