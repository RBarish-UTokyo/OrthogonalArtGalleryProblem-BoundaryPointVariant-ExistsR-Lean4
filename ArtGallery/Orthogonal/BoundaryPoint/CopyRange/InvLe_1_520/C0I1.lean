module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange
public import ArtGallery.Orthogonal.BoundaryPoint.RegChain
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.InvLe_1_520
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_520.C0Defs

/-! Range data of profile `InvLe_1_520`: `C0I1` (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_520
open MarginCert RegisterTable RegisterOrder KronCert IndexedWing ShapeRefs RoomCoordinates CopyChannel CopyMatch CopyRange
open WingOrder.InvLe_1_520
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def c0L2L : Ex := (.lit ([[[2462517657600],[-128256128000]],[],[[1281280]]] : P3))

noncomputable def c0L2X30N : Ex := c0N250
noncomputable def c0L2X30D : Ex := c0D250
noncomputable def c0L2X30C : Ex := (.lit ([[[5005]]] : P3))

theorem c0L2X30cof : RegCert.auto (.sub (.mul c0L2X30D c0L2X30C) c0L2L)=true := by decide +kernel

noncomputable def c0L2X44N : Ex := c0N826
noncomputable def c0L2X44D : Ex := c0D826
noncomputable def c0L2X44C : Ex := (.lit ([[[1231258828800],[-64128064000]],[],[[640640]]] : P3))

theorem c0L2X44cof : RegCert.auto (.sub (.mul c0L2X44D c0L2X44C) c0L2L)=true := by decide +kernel

noncomputable def c0L2X45N : Ex := (.lit ([[[4934930]],[],[[1]]] : P3))
noncomputable def c0L2X45D : Ex := (.lit ([[[20020]]] : P3))
noncomputable def c0L2X45C : Ex := (.lit ([[[123002880],[-6406400]],[],[[64]]] : P3))

theorem c0L2X45cof : RegCert.auto (.sub (.mul c0L2X45D c0L2X45C) c0L2L)=true := by decide +kernel

noncomputable def c0L2Y1N : Ex := (.lit ([[[-4]]] : P3))
noncomputable def c0L2Y1D : Ex := (.lit ([[[1]]] : P3))
noncomputable def c0L2Y1C : Ex := (.lit ([[[2462517657600],[-128256128000]],[],[[1281280]]] : P3))

theorem c0L2Y1cof : RegCert.auto (.sub (.mul c0L2Y1D c0L2Y1C) c0L2L)=true := by decide +kernel

noncomputable def c0L2Y13N : Ex := c0N812
noncomputable def c0L2Y13D : Ex := c0D812
noncomputable def c0L2Y13C : Ex := (.lit ([[[2462517657600],[-128256128000]],[],[[1281280]]] : P3))

theorem c0L2Y13cof : RegCert.auto (.sub (.mul c0L2Y13D c0L2Y13C) c0L2L)=true := by decide +kernel

noncomputable def c0L2Y37N : Ex := c0N579
noncomputable def c0L2Y37D : Ex := c0D579
noncomputable def c0L2Y37C : Ex := (.lit ([[[80080]]] : P3))

theorem c0L2Y37cof : RegCert.auto (.sub (.mul c0L2Y37D c0L2Y37C) c0L2L)=true := by decide +kernel

noncomputable def c0L2P : Ex := (.sp ⟨2,0,[(75,6,SP.join 8000 [0x2fc77520100000500000091f4c6036900000010300000af25ba6a7e0001000003006f77912126b65200100020110b855c4f901bf80000000101a0833762f010c800001000001])]⟩)

theorem c0L2ok : signed (1/65:ℚ) (4/5005:ℚ) (509/130130:ℚ) (detX (.mul c0L2X45N c0L2X45C) (.mul c0L2Y1N c0L2Y1C) (.mul c0L2X44N c0L2X44C) (.mul c0L2Y13N c0L2Y13C) (.mul c0L2X30N c0L2X30C) (.mul c0L2Y37N c0L2Y37C)) c0L2P (-1)=true := by decide +kernel

noncomputable def c0L2K : Ex := (.lit ([[[1]]] : P3))

theorem c0L2Lne : RegCert.auto (.sub (.mul c0L2L c0L2K) (.mul c0L2X30D (.lit [[[5005]]])))=true := by decide +kernel




noncomputable def c0deepL : Ex := (.sp ⟨1,0,[(64,9,SP.join 8000 [0x19000000000b0000000001e8c500000005000000098bd90000400042400000ce331c00000000012000005d5190c28010001080000cf71f4830000000004015df1ded9600000400041cfc3026a13990000000000fcea9bc6bcf0c0001000106]),(108,9,SP.join 8000 [0x3e0a06bdde3a8000000000060000000101f49aa96ce5590000080008280000009b9bc3f3b6bb9e00000000000140000053844b7ddb88dc0000000200020800003c21cff437aa38000000000000004000028d20965e3ed44878000000800081800187e05a388c18f8480000000000000c1e9d870c6af1f365a000000000200020525e843aa6912ba3600000000000000002])]⟩)

noncomputable def c0deepY38N : Ex := c0N229
noncomputable def c0deepY38D : Ex := c0D229
noncomputable def c0deepY38C : Ex := (.lit ([[],[],[[1]]] : P3))

theorem c0deepY38cof : RegCert.auto (.sub (.mul c0deepY38D c0deepY38C) c0deepL)=true := by decide +kernel

noncomputable def c0deeponeN : Ex := (.lit ([[[1]]] : P3))
noncomputable def c0deeponeD : Ex := (.lit ([[[1]]] : P3))
noncomputable def c0deeponeC : Ex := (.sp ⟨1,0,[(64,9,SP.join 8000 [0x19000000000b0000000001e8c500000005000000098bd90000400042400000ce331c00000000012000005d5190c28010001080000cf71f4830000000004015df1ded9600000400041cfc3026a13990000000000fcea9bc6bcf0c0001000106]),(108,9,SP.join 8000 [0x3e0a06bdde3a8000000000060000000101f49aa96ce5590000080008280000009b9bc3f3b6bb9e00000000000140000053844b7ddb88dc0000000200020800003c21cff437aa38000000000000004000028d20965e3ed44878000000800081800187e05a388c18f8480000000000000c1e9d870c6af1f365a000000000200020525e843aa6912ba3600000000000000002])]⟩)

theorem c0deeponecof : RegCert.auto (.sub (.mul c0deeponeD c0deeponeC) c0deepL)=true := by decide +kernel

noncomputable def c0deepvDN : Ex := (.lit ([[[50050]]] : P3))
noncomputable def c0deepvDD : Ex := (.lit ([[],[],[[1]]] : P3))
noncomputable def c0deepvDC : Ex := (.sp ⟨1,0,[(64,9,SP.join 8000 [0x1900000000090000000001e8c500000004000000098bd90000400041c00000ce331c0000000000e000005d5190c28010001060000cf71f4830000000003015df1ded96000004000414fc3026a13990000000000bcea9bc6bcf0c0001000104]),(108,9,SP.join 8000 [0x3e0a06bdde3a8000000000040000000101f49aa96ce5590000080008180000009b9bc3f3b6bb9e000000000000c0000053844b7ddb88dc0000000200020400003c21cff437aa38000000000000002000028d20965e3ed44878000000800080800187e05a388c18f848000000000000041e9d870c6af1f365a000000000200020125e843aa6912ba3600000000000000000])]⟩)

theorem c0deepvDcof : RegCert.auto (.sub (.mul c0deepvDD c0deepvDC) c0deepL)=true := by decide +kernel

noncomputable def c0deepP : Ex := (.sp ⟨3,0,[(69,8,SP.join 8000 [0x9600000400005c00000728e2c000000000115000055b85a49abe80400005400006ffb7a830000000011405cef440c3162700040000500577c77b658000001000213c78927437bfba2c00000044cab0ad80bff0c00001000212]),(111,14,SP.join 8000 [0x562c509dbb5115f7c01000013000000027a481a76d8fe2d2d00000001120000008bb3cae69338d42c9480010000120000001a34375207cadedf13200100021100000907cac44b5ed13ae1b9a0000001110000d18af3ad82758eab62658001000011000064a407cfa4b6e288e924000100021000a7f6bbb2b66fad27b2ca3e000000011013b52c9b50b1c0062ebc214000010000100000028d20965e3ed4487800000000030f02cf2176d77de14b06b66beec00100020ff39086909bc649e75cf1d21e000000010f007aa3711c06390b490fa430000000030ecb409e745767111c5e1acc00000000030d]),(144,13,SP.join 8000 [0x16224e42cb4d03f3e4e9093d80000100000f0000000949dfacd905d6e936428f9c3c0000800107000003c7d4da404fdcbaa49d1be6844000000000438000292a8565338967ed6317eeac88c00000200001c0000232c620a243b4f1540e6ab3da7a0000100020d0008ff0768001a1244c8da662787708000000000868069ecdf0cea5669c3733248479368000000400003400002d1a55bddf1f7f008993caa44640000000061800f7bcf013a7c0c75fd33f99306ebc00000100020c45e5878c59626d385fd3f85c9a490c00000000008600056e45f628d2a8257172fd57bcf00000000000c2e051a925e4b4c2ad0b8ade1f84424c000000200041720e40a118b9f7ce7112a75b2ecb8f000000000030a]),(171,12,SP.join 8000 [0xa042eb604cdacd17cbf12fd1f38820000000100000c00000ef24c392d75e548bf3c6d61aac3b6e0000000000010b000146f247c321364dd182270f907e8b9600000000100000b0000461dc342c6e67c5b7c934dedbf0a3940000000100020a0020bb1381cee69be9488f1fc8e91a073f40000000000010a02388a11f158717eafe8ad735140c4a91800000000100000a000010df03e166cdc11a2f535aea0c91d1e800000000003090065707a9205249b47d0b488a04472570a40000000100020970215651cd3d1f9a19f346662e896f7470000000000000109004a1434294aabd52c37b157a71841740000000000000030845e1a161069b91fd96ec39878f552f3bc000000000100020886ff5853e0af3aaf10a259d6aa4f15082c000000000000307]),(201,13,SP.join 8000 [0x893df0bdd50445343cab498eb1e164f43000000000010000090000011345a8c0dd6f2adc1ac32720f543e40fb40000000000000042000005c5f87ee0d76c495d303a80f76e5bbcc9a00000000000100000800000587ae55630a9d2165b5cfa4940f950c4d198000000000400081c001503a3f3ac169c0beeb7f23b69bc2ae44b45000000000000000107005dc6c5cd7405a576243bc64360b0461b9ffa000000000000400001c000002eeac27e6a3fbb5655ebf399fc1ddde240000000000000003060000e811be0f398a2269647d3eddf23c4e5e87000000000000000081817206fae655fcf92e68243f17f366c2b0fd2100000000000000001067ba10c6a621324082e535352e73c6efa68ff800000000000004000018001f3e4942d9eec60edfb78ce93de9450e000000000000000000030501936ddec8d14190a00f254b83bc3a7ede600000000000000000008167327391b0f499cbd9113a00982c6bb20f70000000000000000000105]),(231,10,SP.join 8000 [0x3b7ce8a1bc5e187ef1f997290708a567322000000000000000010000050000001e8cc4ac61cb283a3d99e64895cd62fd0778a10000000000000000020400003fd6a9afc4a40d406309746b65efc39a3ad44e40000000000000000001040004f5b108646b0bf0ad36dad3a9c493ddf3558fbc0000000000000001000004000003ba6c695cfe0de4ac3e80cdc0d815024d3c60000000000000000000020300008f29dc9abfb548b36fc68543539cc05862a800000000000000000100010300055e5eac33fd32b9edcaa4ff5322ad9cea198000000000000000000000000300597a29e0b7d14d7025dc134a1441f8373da9000000000000000000000002020d6becae81f8fed0d27a9c7e4fd6b208493fc00000000000000000000100010280d8e024dfbcc16e4aff77efcb4046b5f2640000000000000000000000000002])]⟩)

theorem c0deepok : signed (1/65:ℚ) (4/5005:ℚ) (509/130130:ℚ) (linX (.mul c0deeponeN c0deeponeC) [(1,(.mul c0deepvDN c0deepvDC)),(-1,(.mul c0deepY38N c0deepY38C)),(1,(.mul c0deeponeN c0deeponeC))]) c0deepP (1)=true := by decide +kernel

noncomputable def c0deepK : Ex := (.lit ([[[1]]] : P3))

theorem c0deepLne : RegCert.auto (.sub (.mul c0deepL c0deepK) (.mul c0deepY38D c0deepvDD))=true := by decide +kernel




noncomputable def c0H43L : Ex := (.lit ([[[30750720],[-1601600]],[],[[16]]] : P3))

noncomputable def c0H43Y37N : Ex := c0N579
noncomputable def c0H43Y37D : Ex := c0D579
noncomputable def c0H43Y37C : Ex := (.lit ([[[1]]] : P3))

theorem c0H43Y37cof : RegCert.auto (.sub (.mul c0H43Y37D c0H43Y37C) c0H43L)=true := by decide +kernel

noncomputable def c0H43oneN : Ex := (.lit ([[[1]]] : P3))
noncomputable def c0H43oneD : Ex := (.lit ([[[1]]] : P3))
noncomputable def c0H43oneC : Ex := (.lit ([[[30750720],[-1601600]],[],[[16]]] : P3))

theorem c0H43onecof : RegCert.auto (.sub (.mul c0H43oneD c0H43oneC) c0H43L)=true := by decide +kernel

noncomputable def c0H43P : Ex := (.sp ⟨2,0,[(55,9,SP.join 8000 [0x801000004000000000754e1000003000000187040000001020000038e071c0000000200000b32bf73800001010000d7018f10010000010012a9e9c08001000200056dfb13e07001000100831fd35fa20000000000])]⟩)

theorem c0H43ok : signed (1/65:ℚ) (4/5005:ℚ) (509/130130:ℚ) (linX (.mul c0H43oneN c0H43oneC) [(3,(.mul c0H43Y37N c0H43Y37C)),(-7,(.mul c0H43oneN c0H43oneC))]) c0H43P (1)=true := by decide +kernel

noncomputable def c0H43K : Ex := (.lit ([[[1]]] : P3))

theorem c0H43Lne : RegCert.auto (.sub (.mul c0H43L c0H43K) c0H43Y37D)=true := by decide +kernel

end ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_520
end
