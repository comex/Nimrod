/* Generated by Nimrod Compiler v0.8.9 */
/*   (c) 2010 Andreas Rumpf */

typedef long long int NI;
typedef unsigned long long int NU;
#include "nimbase.h"

typedef struct TY98008 TY98008;
typedef struct TGenericSeq TGenericSeq;
typedef struct TNimType TNimType;
typedef struct TNimNode TNimNode;
struct TGenericSeq {
NI len;
NI space;
};
struct TNimType {
NI size;
NU8 kind;
NU8 flags;
TNimType* base;
TNimNode* node;
void* finalizer;
};
struct TNimNode {
NU8 kind;
NI offset;
TNimType* typ;
NCSTRING name;
NI len;
TNimNode** sons;
};
struct TY98008 {
  TGenericSeq Sup;
  NI8 data[SEQ_DECL_SIZE];
};
N_NIMCALL(NIM_BOOL, Bitsetin_98045)(TY98008* X_98047, NI64 E_98048);
static N_INLINE(NI64, divInt64)(NI64 A_5761, NI64 B_5762);
N_NOINLINE(void, raiseDivByZero)(void);
N_NOINLINE(void, raiseOverflow)(void);
N_NOINLINE(void, raiseIndexError)(void);
static N_INLINE(NI64, modInt64)(NI64 A_5772, NI64 B_5773);
N_NIMCALL(void, Bitsetincl_98035)(TY98008** X_98038, NI64 Elem_98039);
N_NIMCALL(void, internalAssert)(NCSTRING File_5254, NI Line_5255, NIM_BOOL Cond_5256);
N_NIMCALL(void, Bitsetexcl_98040)(TY98008** X_98043, NI64 Elem_98044);
N_NIMCALL(void, Bitsetinit_98010)(TY98008** B_98013, NI Length_98014);
N_NIMCALL(void*, newSeq)(TNimType* Typ_12804, NI Len_12805);
N_NIMCALL(void, unsureAsgnRef)(void** Dest_11826, void* Src_11827);
N_NIMCALL(void, Bitsetunion_98015)(TY98008** X_98018, TY98008* Y_98019);
static N_INLINE(NI, addInt)(NI A_5803, NI B_5804);
N_NIMCALL(void, Bitsetdiff_98020)(TY98008** X_98023, TY98008* Y_98024);
N_NIMCALL(void, Bitsetsymdiff_98025)(TY98008** X_98028, TY98008* Y_98029);
N_NIMCALL(void, Bitsetintersect_98030)(TY98008** X_98033, TY98008* Y_98034);
N_NIMCALL(NIM_BOOL, Bitsetequals_98049)(TY98008* X_98051, TY98008* Y_98052);
N_NIMCALL(NIM_BOOL, Bitsetcontains_98053)(TY98008* X_98055, TY98008* Y_98056);
extern TNimType* NTI98008; /* TBitSet */
static N_INLINE(NI64, divInt64)(NI64 A_5761, NI64 B_5762) {
NI64 Result_5763;
NIM_BOOL LOC5;
Result_5763 = 0;
if (!(B_5762 == 0)) goto LA2;
raiseDivByZero();
LA2: ;
LOC5 = (A_5761 == (IL64(-9223372036854775807) - IL64(1)));
if (!(LOC5)) goto LA6;
LOC5 = (B_5762 == -1);
LA6: ;
if (!LOC5) goto LA7;
raiseOverflow();
LA7: ;
Result_5763 = (NI64)(A_5761 / B_5762);
goto BeforeRet;
BeforeRet: ;
return Result_5763;
}
static N_INLINE(NI64, modInt64)(NI64 A_5772, NI64 B_5773) {
NI64 Result_5774;
Result_5774 = 0;
if (!(B_5773 == 0)) goto LA2;
raiseDivByZero();
LA2: ;
Result_5774 = (NI64)(A_5772 % B_5773);
goto BeforeRet;
BeforeRet: ;
return Result_5774;
}
N_NIMCALL(NIM_BOOL, Bitsetin_98045)(TY98008* X_98047, NI64 E_98048) {
NIM_BOOL Result_98061;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "BitSetIn";
F.prev = framePtr;
F.filename = "rod/bitsets.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_98061 = 0;
F.line = 34;F.filename = "bitsets.nim";
if ((NU)(divInt64(E_98048, 8)) >= (NU)(X_98047->Sup.len)) raiseIndexError();
Result_98061 = !(((NI8)(X_98047->data[divInt64(E_98048, 8)] & ((NI8)(NU8)(NU)(((NI) ((NI64)((NU64)(1) << (NU64)(modInt64(E_98048, 8)))))))) == ((NI8) 0)));
framePtr = framePtr->prev;
return Result_98061;
}
N_NIMCALL(void, Bitsetincl_98035)(TY98008** X_98038, NI64 Elem_98039) {
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "BitSetIncl";
F.prev = framePtr;
F.filename = "rod/bitsets.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 38;F.filename = "bitsets.nim";
internalAssert("rod/bitsets.nim", 38, (0 <= Elem_98039));
F.line = 39;F.filename = "bitsets.nim";
if ((NU)(divInt64(Elem_98039, 8)) >= (NU)((*X_98038)->Sup.len)) raiseIndexError();
if ((NU)(divInt64(Elem_98039, 8)) >= (NU)((*X_98038)->Sup.len)) raiseIndexError();
(*X_98038)->data[divInt64(Elem_98039, 8)] = (NI8)((*X_98038)->data[divInt64(Elem_98039, 8)] | ((NI8)(NU8)(NU)(((NI) ((NI64)((NU64)(1) << (NU64)(modInt64(Elem_98039, 8))))))));
framePtr = framePtr->prev;
}
N_NIMCALL(void, Bitsetexcl_98040)(TY98008** X_98043, NI64 Elem_98044) {
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "BitSetExcl";
F.prev = framePtr;
F.filename = "rod/bitsets.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 43;F.filename = "bitsets.nim";
if ((NU)(divInt64(Elem_98044, 8)) >= (NU)((*X_98043)->Sup.len)) raiseIndexError();
if ((NU)(divInt64(Elem_98044, 8)) >= (NU)((*X_98043)->Sup.len)) raiseIndexError();
(*X_98043)->data[divInt64(Elem_98044, 8)] = (NI8)((*X_98043)->data[divInt64(Elem_98044, 8)] & (NI8)((NU8) ~(((NI8)(NU8)(NU)(((NI) ((NI64)((NU64)(1) << (NU64)(modInt64(Elem_98044, 8))))))))));
framePtr = framePtr->prev;
}
N_NIMCALL(void, Bitsetinit_98010)(TY98008** B_98013, NI Length_98014) {
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "BitSetInit";
F.prev = framePtr;
F.filename = "rod/bitsets.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 47;F.filename = "bitsets.nim";
unsureAsgnRef((void**) &(*B_98013), (TY98008*) newSeq(NTI98008, Length_98014));
framePtr = framePtr->prev;
}
static N_INLINE(NI, addInt)(NI A_5803, NI B_5804) {
NI Result_5805;
NIM_BOOL LOC2;
Result_5805 = 0;
Result_5805 = (NI64)((NU64)(A_5803) + (NU64)(B_5804));
LOC2 = (0 <= (NI64)(Result_5805 ^ A_5803));
if (LOC2) goto LA3;
LOC2 = (0 <= (NI64)(Result_5805 ^ B_5804));
LA3: ;
if (!LOC2) goto LA4;
goto BeforeRet;
LA4: ;
raiseOverflow();
BeforeRet: ;
return Result_5805;
}
N_NIMCALL(void, Bitsetunion_98015)(TY98008** X_98018, TY98008* Y_98019) {
NI I_98120;
NI HEX3Atmp_98122;
NI Res_98124;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "BitSetUnion";
F.prev = framePtr;
F.filename = "rod/bitsets.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
I_98120 = 0;
HEX3Atmp_98122 = 0;
F.line = 50;F.filename = "bitsets.nim";
HEX3Atmp_98122 = ((*X_98018)->Sup.len-1);
Res_98124 = 0;
F.line = 1021;F.filename = "system.nim";
Res_98124 = 0;
F.line = 1022;F.filename = "system.nim";
while (1) {
if (!(Res_98124 <= HEX3Atmp_98122)) goto LA1;
F.line = 1021;F.filename = "system.nim";
I_98120 = Res_98124;
F.line = 50;F.filename = "bitsets.nim";
if ((NU)(I_98120) >= (NU)((*X_98018)->Sup.len)) raiseIndexError();
if ((NU)(I_98120) >= (NU)((*X_98018)->Sup.len)) raiseIndexError();
if ((NU)(I_98120) >= (NU)(Y_98019->Sup.len)) raiseIndexError();
(*X_98018)->data[I_98120] = (NI8)((*X_98018)->data[I_98120] | Y_98019->data[I_98120]);
F.line = 1024;F.filename = "system.nim";
Res_98124 = addInt(Res_98124, 1);
} LA1: ;
framePtr = framePtr->prev;
}
N_NIMCALL(void, Bitsetdiff_98020)(TY98008** X_98023, TY98008* Y_98024) {
NI I_98139;
NI HEX3Atmp_98141;
NI Res_98143;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "BitSetDiff";
F.prev = framePtr;
F.filename = "rod/bitsets.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
I_98139 = 0;
HEX3Atmp_98141 = 0;
F.line = 53;F.filename = "bitsets.nim";
HEX3Atmp_98141 = ((*X_98023)->Sup.len-1);
Res_98143 = 0;
F.line = 1021;F.filename = "system.nim";
Res_98143 = 0;
F.line = 1022;F.filename = "system.nim";
while (1) {
if (!(Res_98143 <= HEX3Atmp_98141)) goto LA1;
F.line = 1021;F.filename = "system.nim";
I_98139 = Res_98143;
F.line = 53;F.filename = "bitsets.nim";
if ((NU)(I_98139) >= (NU)((*X_98023)->Sup.len)) raiseIndexError();
if ((NU)(I_98139) >= (NU)((*X_98023)->Sup.len)) raiseIndexError();
if ((NU)(I_98139) >= (NU)(Y_98024->Sup.len)) raiseIndexError();
(*X_98023)->data[I_98139] = (NI8)((*X_98023)->data[I_98139] & (NI8)((NU8) ~(Y_98024->data[I_98139])));
F.line = 1024;F.filename = "system.nim";
Res_98143 = addInt(Res_98143, 1);
} LA1: ;
framePtr = framePtr->prev;
}
N_NIMCALL(void, Bitsetsymdiff_98025)(TY98008** X_98028, TY98008* Y_98029) {
NI I_98158;
NI HEX3Atmp_98160;
NI Res_98162;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "BitSetSymDiff";
F.prev = framePtr;
F.filename = "rod/bitsets.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
I_98158 = 0;
HEX3Atmp_98160 = 0;
F.line = 56;F.filename = "bitsets.nim";
HEX3Atmp_98160 = ((*X_98028)->Sup.len-1);
Res_98162 = 0;
F.line = 1021;F.filename = "system.nim";
Res_98162 = 0;
F.line = 1022;F.filename = "system.nim";
while (1) {
if (!(Res_98162 <= HEX3Atmp_98160)) goto LA1;
F.line = 1021;F.filename = "system.nim";
I_98158 = Res_98162;
F.line = 56;F.filename = "bitsets.nim";
if ((NU)(I_98158) >= (NU)((*X_98028)->Sup.len)) raiseIndexError();
if ((NU)(I_98158) >= (NU)((*X_98028)->Sup.len)) raiseIndexError();
if ((NU)(I_98158) >= (NU)(Y_98029->Sup.len)) raiseIndexError();
(*X_98028)->data[I_98158] = (NI8)((*X_98028)->data[I_98158] ^ Y_98029->data[I_98158]);
F.line = 1024;F.filename = "system.nim";
Res_98162 = addInt(Res_98162, 1);
} LA1: ;
framePtr = framePtr->prev;
}
N_NIMCALL(void, Bitsetintersect_98030)(TY98008** X_98033, TY98008* Y_98034) {
NI I_98177;
NI HEX3Atmp_98179;
NI Res_98181;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "BitSetIntersect";
F.prev = framePtr;
F.filename = "rod/bitsets.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
I_98177 = 0;
HEX3Atmp_98179 = 0;
F.line = 59;F.filename = "bitsets.nim";
HEX3Atmp_98179 = ((*X_98033)->Sup.len-1);
Res_98181 = 0;
F.line = 1021;F.filename = "system.nim";
Res_98181 = 0;
F.line = 1022;F.filename = "system.nim";
while (1) {
if (!(Res_98181 <= HEX3Atmp_98179)) goto LA1;
F.line = 1021;F.filename = "system.nim";
I_98177 = Res_98181;
F.line = 59;F.filename = "bitsets.nim";
if ((NU)(I_98177) >= (NU)((*X_98033)->Sup.len)) raiseIndexError();
if ((NU)(I_98177) >= (NU)((*X_98033)->Sup.len)) raiseIndexError();
if ((NU)(I_98177) >= (NU)(Y_98034->Sup.len)) raiseIndexError();
(*X_98033)->data[I_98177] = (NI8)((*X_98033)->data[I_98177] & Y_98034->data[I_98177]);
F.line = 1024;F.filename = "system.nim";
Res_98181 = addInt(Res_98181, 1);
} LA1: ;
framePtr = framePtr->prev;
}
N_NIMCALL(NIM_BOOL, Bitsetequals_98049)(TY98008* X_98051, TY98008* Y_98052) {
NIM_BOOL Result_98188;
NI I_98196;
NI HEX3Atmp_98200;
NI Res_98202;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "BitSetEquals";
F.prev = framePtr;
F.filename = "rod/bitsets.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_98188 = 0;
I_98196 = 0;
HEX3Atmp_98200 = 0;
F.line = 62;F.filename = "bitsets.nim";
HEX3Atmp_98200 = (X_98051->Sup.len-1);
Res_98202 = 0;
F.line = 1021;F.filename = "system.nim";
Res_98202 = 0;
F.line = 1022;F.filename = "system.nim";
while (1) {
if (!(Res_98202 <= HEX3Atmp_98200)) goto LA1;
F.line = 1021;F.filename = "system.nim";
I_98196 = Res_98202;
F.line = 63;F.filename = "bitsets.nim";
if ((NU)(I_98196) >= (NU)(X_98051->Sup.len)) raiseIndexError();
if ((NU)(I_98196) >= (NU)(Y_98052->Sup.len)) raiseIndexError();
if (!!((X_98051->data[I_98196] == Y_98052->data[I_98196]))) goto LA3;
F.line = 64;F.filename = "bitsets.nim";
F.line = 64;F.filename = "bitsets.nim";
Result_98188 = NIM_FALSE;
goto BeforeRet;
LA3: ;
F.line = 1024;F.filename = "system.nim";
Res_98202 = addInt(Res_98202, 1);
} LA1: ;
F.line = 65;F.filename = "bitsets.nim";
Result_98188 = NIM_TRUE;
BeforeRet: ;
framePtr = framePtr->prev;
return Result_98188;
}
N_NIMCALL(NIM_BOOL, Bitsetcontains_98053)(TY98008* X_98055, TY98008* Y_98056) {
NIM_BOOL Result_98209;
NI I_98217;
NI HEX3Atmp_98221;
NI Res_98223;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "BitSetContains";
F.prev = framePtr;
F.filename = "rod/bitsets.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_98209 = 0;
I_98217 = 0;
HEX3Atmp_98221 = 0;
F.line = 68;F.filename = "bitsets.nim";
HEX3Atmp_98221 = (X_98055->Sup.len-1);
Res_98223 = 0;
F.line = 1021;F.filename = "system.nim";
Res_98223 = 0;
F.line = 1022;F.filename = "system.nim";
while (1) {
if (!(Res_98223 <= HEX3Atmp_98221)) goto LA1;
F.line = 1021;F.filename = "system.nim";
I_98217 = Res_98223;
F.line = 69;F.filename = "bitsets.nim";
if ((NU)(I_98217) >= (NU)(X_98055->Sup.len)) raiseIndexError();
if ((NU)(I_98217) >= (NU)(Y_98056->Sup.len)) raiseIndexError();
if (!!(((NI8)(X_98055->data[I_98217] & (NI8)((NU8) ~(Y_98056->data[I_98217]))) == ((NI8) 0)))) goto LA3;
F.line = 70;F.filename = "bitsets.nim";
F.line = 70;F.filename = "bitsets.nim";
Result_98209 = NIM_FALSE;
goto BeforeRet;
LA3: ;
F.line = 1024;F.filename = "system.nim";
Res_98223 = addInt(Res_98223, 1);
} LA1: ;
F.line = 71;F.filename = "bitsets.nim";
Result_98209 = NIM_TRUE;
BeforeRet: ;
framePtr = framePtr->prev;
return Result_98209;
}
N_NOINLINE(void, bitsetsInit)(void) {
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "bitsets";
F.prev = framePtr;
F.filename = "rod/bitsets.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
framePtr = framePtr->prev;
}

