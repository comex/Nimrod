/* Generated by Nimrod Compiler v0.8.9 */
/*   (c) 2010 Andreas Rumpf */

typedef long int NI;
typedef unsigned long int NU;
#include "nimbase.h"

typedef struct TY57223 TY57223;
typedef struct TY57221 TY57221;
typedef struct TY57219 TY57219;
typedef struct TGenericSeq TGenericSeq;
typedef struct TNimType TNimType;
typedef struct TNimNode TNimNode;
typedef struct TY53545 TY53545;
typedef struct TY53527 TY53527;
typedef struct TY53525 TY53525;
typedef struct TY52011 TY52011;
typedef struct TY52005 TY52005;
typedef struct TNimObject TNimObject;
typedef struct NimStringDesc NimStringDesc;
typedef struct TY53549 TY53549;
typedef struct TY45532 TY45532;
typedef struct TY53523 TY53523;
typedef struct TY53537 TY53537;
typedef struct TY50008 TY50008;
typedef struct TY53541 TY53541;
typedef struct TY10402 TY10402;
typedef struct TY10414 TY10414;
typedef struct TY10790 TY10790;
typedef struct TY10418 TY10418;
typedef struct TY10410 TY10410;
typedef struct TY10788 TY10788;
typedef struct TY57079 TY57079;
typedef struct TY53561 TY53561;
typedef struct TY53559 TY53559;
typedef struct TY53557 TY53557;
typedef struct TY57107 TY57107;
typedef struct TY57109 TY57109;
typedef struct TY57092 TY57092;
typedef struct TY53567 TY53567;
typedef struct TY53565 TY53565;
typedef struct TY53563 TY53563;
typedef struct TY53517 TY53517;
typedef struct TY53547 TY53547;
typedef struct TY41013 TY41013;
struct TY57219 {
NI Key;
NI Val;
};
struct TGenericSeq {
NI len;
NI space;
};
struct TY57223 {
NI Counter;
TY57221* Data;
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
struct TY53527 {
TNimType* m_type;
NI Counter;
TY53525* Data;
};
struct TNimObject {
TNimType* m_type;
};
struct TY52005 {
  TNimObject Sup;
NI Id;
};
typedef NIM_CHAR TY239[100000001];
struct NimStringDesc {
  TGenericSeq Sup;
TY239 data;
};
struct TY52011 {
  TY52005 Sup;
NimStringDesc* S;
TY52011* Next;
NI H;
};
struct TY45532 {
NI16 Line;
NI16 Col;
int Fileindex;
};
struct TY53537 {
NU8 K;
NU8 S;
NU8 Flags;
TY53549* T;
TY50008* R;
NI A;
};
struct TY53545 {
  TY52005 Sup;
NU8 Kind;
NU8 Magic;
TY53549* Typ;
TY52011* Name;
TY45532 Info;
TY53545* Owner;
NU32 Flags;
TY53527 Tab;
TY53523* Ast;
NU32 Options;
NI Position;
NI Offset;
TY53537 Loc;
TY53541* Annex;
};
struct TY10402 {
NI Refcount;
TNimType* Typ;
};
struct TY10418 {
NI Len;
NI Cap;
TY10402** D;
};
struct TY10414 {
NI Counter;
NI Max;
TY10410* Head;
TY10410** Data;
};
struct TY10788 {
NI Stackscans;
NI Cyclecollections;
NI Maxthreshold;
NI Maxstacksize;
NI Maxstackcells;
NI Cycletablesize;
};
struct TY10790 {
TY10418 Zct;
TY10418 Decstack;
TY10414 Cycleroots;
TY10418 Tempstack;
TY10788 Stat;
};
struct TY57079 {
NI H;
};
struct TY53557 {
TY52005* Key;
TNimObject* Val;
};
struct TY53561 {
NI Counter;
TY53559* Data;
};
struct TY57107 {
NI Tos;
TY57109* Stack;
};
struct TY57092 {
NI H;
TY52011* Name;
};
struct TY53563 {
TY52005* Key;
TY53523* Val;
};
struct TY53567 {
NI Counter;
TY53565* Data;
};
struct TY53523 {
TY53549* Typ;
NimStringDesc* Comment;
TY45532 Info;
NU8 Flags;
NU8 Kind;
union {
struct {NI64 Intval;
} S1;
struct {NF64 Floatval;
} S2;
struct {NimStringDesc* Strval;
} S3;
struct {TY53545* Sym;
} S4;
struct {TY52011* Ident;
} S5;
struct {TY53517* Sons;
} S6;
} KindU;
};
struct TY53549 {
  TY52005 Sup;
NU8 Kind;
TY53547* Sons;
TY53523* N;
NU8 Flags;
NU8 Callconv;
TY53545* Owner;
TY53545* Sym;
NI64 Size;
NI Align;
NI Containerid;
TY53537 Loc;
};
struct TY50008 {
  TNimObject Sup;
TY50008* Left;
TY50008* Right;
NI Length;
NimStringDesc* Data;
};
struct TY41013 {
  TNimObject Sup;
TY41013* Prev;
TY41013* Next;
};
struct TY53541 {
  TY41013 Sup;
NU8 Kind;
NIM_BOOL Generated;
TY50008* Name;
TY53523* Path;
};
typedef NI TY8414[16];
struct TY10410 {
TY10410* Next;
NI Key;
TY8414 Bits;
};
struct TY57221 {
  TGenericSeq Sup;
  TY57219 data[SEQ_DECL_SIZE];
};
struct TY53525 {
  TGenericSeq Sup;
  TY53545* data[SEQ_DECL_SIZE];
};
struct TY53559 {
  TGenericSeq Sup;
  TY53557 data[SEQ_DECL_SIZE];
};
struct TY57109 {
  TGenericSeq Sup;
  TY53527 data[SEQ_DECL_SIZE];
};
struct TY53565 {
  TGenericSeq Sup;
  TY53563 data[SEQ_DECL_SIZE];
};
struct TY53517 {
  TGenericSeq Sup;
  TY53523* data[SEQ_DECL_SIZE];
};
struct TY53547 {
  TGenericSeq Sup;
  TY53549* data[SEQ_DECL_SIZE];
};
N_NIMCALL(void*, newSeq)(TNimType* Typ_12603, NI Len_12604);
N_NIMCALL(void, unsureAsgnRef)(void** Dest_11622, void* Src_11623);
N_NIMCALL(NI, Nexttry_57213)(NI H_57215, NI Maxhash_57216);
N_NIMCALL(NIM_BOOL, Mustrehash_57209)(NI Length_57211, NI Counter_57212);
N_NIMCALL(void, Strtableenlarge_59357)(TY53527* T_59360);
N_NIMCALL(void, Strtablerawinsert_59311)(TY53525** Data_59314, TY53545* N_59315);
N_NIMCALL(void, Internalerror_45567)(TY45532 Info_45569, NimStringDesc* Errmsg_45570);
static N_INLINE(void, appendString)(NimStringDesc* Dest_17192, NimStringDesc* Src_17193);
N_NIMCALL(NimStringDesc*, rawNewString)(NI Space_17087);
static N_INLINE(void, asgnRef)(void** Dest_11612, void* Src_11613);
static N_INLINE(void, Incref_11601)(TY10402* C_11603);
static N_INLINE(NIM_BOOL, Canbecycleroot_10826)(TY10402* C_10828);
static N_INLINE(void, Rtladdcycleroot_11452)(TY10402* C_11454);
N_NOINLINE(void, Incl_10674)(TY10414* S_10677, TY10402* Cell_10678);
static N_INLINE(TY10402*, Usrtocell_10822)(void* Usr_10824);
static N_INLINE(void, Decref_11460)(TY10402* C_11462);
static N_INLINE(void, Rtladdzct_11456)(TY10402* C_11458);
N_NOINLINE(void, Addzct_10811)(TY10418* S_10814, TY10402* C_10815);
N_NIMCALL(TY53545*, Nextiter_57086)(TY57079* Ti_57089, TY53527* Tab_57090);
N_NIMCALL(NI, Iitablerawget_60157)(TY57223 T_60159, NI Key_60160);
N_NIMCALL(void, Iitablerawinsert_60176)(TY57221** Data_60179, NI Key_60180, NI Val_60181);
N_NIMCALL(NI, Idtablerawget_59778)(TY53561 T_59780, NI Key_59781);
static N_INLINE(void, asgnRefNoCycle)(void** Dest_11616, void* Src_11617);
N_NIMCALL(void, Idtablerawinsert_59831)(TY53559** Data_59834, TY52005* Key_59835, TNimObject* Val_59836);
N_NIMCALL(TY53545*, Strtableget_57069)(TY53527* T_57071, TY52011* Name_57072);
N_NIMCALL(TY53545*, Nextidentiter_57101)(TY57092* Ti_57104, TY53527* Tab_57105);
N_NIMCALL(NI, Idnodetablerawget_59967)(TY53567 T_59969, TY52005* Key_59970);
N_NIMCALL(void, Idnodetablerawinsert_59995)(TY53565** Data_59998, TY52005* Key_59999, TY53523* Val_60000);
N_NIMCALL(NI, Sonslen_53801)(TY53523* N_53803);
N_NIMCALL(TGenericSeq*, setLengthSeq)(TGenericSeq* Seq_17403, NI Elemsize_17404, NI Newlen_17405);
N_NIMCALL(void, Initstrtable_53744)(TY53527* X_53747);
N_NIMCALL(NU8, Symtabadduniqueat_57143)(TY57107* Tab_57146, TY53545* E_57147, NI At_57148);
N_NIMCALL(void, Strtableadd_57064)(TY53527* T_57067, TY53545* N_57068);
N_NIMCALL(NimStringDesc*, Ropetostr_50066)(TY50008* P_50068);
N_NIMCALL(TY50008*, Debugtype_58411)(TY53549* N_58413);
N_NIMCALL(TY50008*, Torope_50046)(NimStringDesc* S_50048);
N_NIMCALL(NimStringDesc*, reprEnum)(NI E_18179, TNimType* Typ_18180);
N_NIMCALL(void, App_50036)(TY50008** A_50039, NimStringDesc* B_50040);
N_NIMCALL(NI, Sonslen_53804)(TY53549* N_53806);
N_NIMCALL(void, App_50031)(TY50008** A_50034, TY50008* B_50035);
N_NIMCALL(TY53545*, Lookupinrecord_57202)(TY53523* N_57204, TY52011* Field_57205);
N_NIMCALL(TY53523*, Lastson_53807)(TY53523* N_53809);
N_NIMCALL(void, Writeln_58812)(FILE* F_58815, NimStringDesc* X_58816);
N_NIMCALL(void, Write_3658)(FILE* F_3660, NimStringDesc* S_3661);
STRING_LITERAL(TMP193621, "StrTableRawInsert: ", 19);
STRING_LITERAL(TMP194056, "getSymFromList", 14);
STRING_LITERAL(TMP194138, "null", 4);
STRING_LITERAL(TMP194139, " ", 1);
STRING_LITERAL(TMP194140, "(", 1);
STRING_LITERAL(TMP194141, ", ", 2);
STRING_LITERAL(TMP194142, ")", 1);
STRING_LITERAL(TMP194681, "lookupInRecord", 14);
STRING_LITERAL(TMP194682, "lookupInRecord(record case branch)", 34);
STRING_LITERAL(TMP194683, "lookupInRecord()", 16);
STRING_LITERAL(TMP195493, "\012", 1);
extern TNimType* NTI57221; /* TIIPairSeq */
extern TNimType* NTI53525; /* TSymSeq */
extern TY10790 Gch_10808;
extern TNimType* NTI53559; /* TIdPairSeq */
extern TNimType* NTI57109; /* seq[TStrTable] */
extern TNimType* NTI53565; /* TIdNodePairSeq */
extern TNimType* NTI53162; /* TTypeKind */
N_NIMCALL(void, Initiitable_57228)(TY57223* X_57231) {
NI I_60151;
NI Res_60154;
(*X_57231).Counter = 0;
unsureAsgnRef((void**) &(*X_57231).Data, (TY57221*) newSeq(NTI57221, 8));
I_60151 = 0;
Res_60154 = 0;
Res_60154 = 0;
while (1) {
if (!(Res_60154 <= 7)) goto LA1;
I_60151 = Res_60154;
(*X_57231).Data->data[I_60151].Key = (-2147483647 -1);
Res_60154 += 1;
} LA1: ;
}
N_NIMCALL(NI, Nexttry_57213)(NI H_57215, NI Maxhash_57216) {
NI Result_58868;
Result_58868 = 0;
Result_58868 = (NI32)((NI32)((NI32)(5 * H_57215) + 1) & Maxhash_57216);
return Result_58868;
}
N_NIMCALL(TY53545*, Strtableget_57069)(TY53527* T_57071, TY52011* Name_57072) {
TY53545* Result_59507;
NI H_59508;
Result_59507 = 0;
H_59508 = 0;
H_59508 = (NI32)((*Name_57072).H & ((*T_57071).Data->Sup.len-1));
while (1) {
Result_59507 = (*T_57071).Data->data[H_59508];
if (!(Result_59507 == NIM_NIL)) goto LA3;
goto LA1;
LA3: ;
if (!((*(*Result_59507).Name).Sup.Id == (*Name_57072).Sup.Id)) goto LA6;
goto LA1;
LA6: ;
H_59508 = Nexttry_57213(H_59508, ((*T_57071).Data->Sup.len-1));
} LA1: ;
return Result_59507;
}
N_NIMCALL(NIM_BOOL, Mustrehash_57209)(NI Length_57211, NI Counter_57212) {
NIM_BOOL Result_57536;
NIM_BOOL LOC1;
Result_57536 = 0;
LOC1 = ((NI32)(Length_57211 * 2) < (NI32)(Counter_57212 * 3));
if (LOC1) goto LA2;
LOC1 = ((NI32)(Length_57211 - Counter_57212) < 4);
LA2: ;
Result_57536 = LOC1;
return Result_57536;
}
static N_INLINE(void, appendString)(NimStringDesc* Dest_17192, NimStringDesc* Src_17193) {
memcpy(((NCSTRING) (&(*Dest_17192).data[((*Dest_17192).Sup.len)-0])), ((NCSTRING) ((*Src_17193).data)), ((int) ((NI32)((NI32)((*Src_17193).Sup.len + 1) * 1))));
(*Dest_17192).Sup.len += (*Src_17193).Sup.len;
}
static N_INLINE(NIM_BOOL, Canbecycleroot_10826)(TY10402* C_10828) {
NIM_BOOL Result_10829;
Result_10829 = 0;
Result_10829 = !((((*(*C_10828).Typ).flags &(1<<((((NU8) 1))&7)))!=0));
return Result_10829;
}
static N_INLINE(void, Rtladdcycleroot_11452)(TY10402* C_11454) {
Incl_10674(&Gch_10808.Cycleroots, C_11454);
}
static N_INLINE(void, Incref_11601)(TY10402* C_11603) {
NIM_BOOL LOC2;
(*C_11603).Refcount = (NI32)((NU32)((*C_11603).Refcount) + (NU32)(8));
LOC2 = Canbecycleroot_10826(C_11603);
if (!LOC2) goto LA3;
Rtladdcycleroot_11452(C_11603);
LA3: ;
}
static N_INLINE(TY10402*, Usrtocell_10822)(void* Usr_10824) {
TY10402* Result_10825;
Result_10825 = 0;
Result_10825 = ((TY10402*) ((NI32)((NU32)(((NI) (Usr_10824))) - (NU32)(((NI) (((NI)sizeof(TY10402))))))));
return Result_10825;
}
static N_INLINE(void, Rtladdzct_11456)(TY10402* C_11458) {
Addzct_10811(&Gch_10808.Zct, C_11458);
}
static N_INLINE(void, Decref_11460)(TY10402* C_11462) {
NIM_BOOL LOC4;
(*C_11462).Refcount = (NI32)((NU32)((*C_11462).Refcount) - (NU32)(8));
if (!((NU32)((*C_11462).Refcount) < (NU32)(8))) goto LA2;
Rtladdzct_11456(C_11462);
goto LA1;
LA2: ;
LOC4 = Canbecycleroot_10826(C_11462);
if (!LOC4) goto LA5;
Rtladdcycleroot_11452(C_11462);
goto LA1;
LA5: ;
LA1: ;
}
static N_INLINE(void, asgnRef)(void** Dest_11612, void* Src_11613) {
TY10402* LOC4;
TY10402* LOC8;
if (!!((Src_11613 == NIM_NIL))) goto LA2;
LOC4 = Usrtocell_10822(Src_11613);
Incref_11601(LOC4);
LA2: ;
if (!!(((*Dest_11612) == NIM_NIL))) goto LA6;
LOC8 = Usrtocell_10822((*Dest_11612));
Decref_11460(LOC8);
LA6: ;
(*Dest_11612) = Src_11613;
}
N_NIMCALL(void, Strtablerawinsert_59311)(TY53525** Data_59314, TY53545* N_59315) {
NI H_59316;
NimStringDesc* LOC5;
H_59316 = 0;
H_59316 = (NI32)((*(*N_59315).Name).H & ((*Data_59314)->Sup.len-1));
while (1) {
if (!!(((*Data_59314)->data[H_59316] == NIM_NIL))) goto LA1;
if (!((*Data_59314)->data[H_59316] == N_59315)) goto LA3;
LOC5 = rawNewString((*(*N_59315).Name).S->Sup.len + 19);
appendString(LOC5, ((NimStringDesc*) &TMP193621));
appendString(LOC5, (*(*N_59315).Name).S);
Internalerror_45567((*N_59315).Info, LOC5);
LA3: ;
H_59316 = Nexttry_57213(H_59316, ((*Data_59314)->Sup.len-1));
} LA1: ;
asgnRef((void**) &(*Data_59314)->data[H_59316], N_59315);
}
N_NIMCALL(void, Strtableenlarge_59357)(TY53527* T_59360) {
TY53525* N_59361;
NI I_59391;
NI HEX3Atmp_59414;
NI Res_59416;
TY53525* LOC5;
N_59361 = 0;
N_59361 = (TY53525*) newSeq(NTI53525, (NI32)((*T_59360).Data->Sup.len * 2));
I_59391 = 0;
HEX3Atmp_59414 = 0;
HEX3Atmp_59414 = ((*T_59360).Data->Sup.len-1);
Res_59416 = 0;
Res_59416 = 0;
while (1) {
if (!(Res_59416 <= HEX3Atmp_59414)) goto LA1;
I_59391 = Res_59416;
if (!!(((*T_59360).Data->data[I_59391] == NIM_NIL))) goto LA3;
Strtablerawinsert_59311(&N_59361, (*T_59360).Data->data[I_59391]);
LA3: ;
Res_59416 += 1;
} LA1: ;
LOC5 = (*T_59360).Data;
unsureAsgnRef((void**) &(*T_59360).Data, N_59361);
N_59361 = LOC5;
}
N_NIMCALL(void, Strtableadd_57064)(TY53527* T_57067, TY53545* N_57068) {
NIM_BOOL LOC2;
LOC2 = Mustrehash_57209((*T_57067).Data->Sup.len, (*T_57067).Counter);
if (!LOC2) goto LA3;
Strtableenlarge_59357(T_57067);
LA3: ;
Strtablerawinsert_59311(&(*T_57067).Data, N_57068);
(*T_57067).Counter += 1;
}
N_NIMCALL(TY53545*, Nextiter_57086)(TY57079* Ti_57089, TY53527* Tab_57090) {
TY53545* Result_59569;
Result_59569 = 0;
Result_59569 = NIM_NIL;
while (1) {
if (!((*Ti_57089).H <= ((*Tab_57090).Data->Sup.len-1))) goto LA1;
Result_59569 = (*Tab_57090).Data->data[(*Ti_57089).H];
(*Ti_57089).H += 1;
if (!!((Result_59569 == NIM_NIL))) goto LA3;
goto LA1;
LA3: ;
} LA1: ;
return Result_59569;
}
N_NIMCALL(TY53545*, Inittabiter_57081)(TY57079* Ti_57084, TY53527* Tab_57085) {
TY53545* Result_59561;
Result_59561 = 0;
(*Ti_57084).H = 0;
if (!((*Tab_57085).Counter == 0)) goto LA2;
Result_59561 = NIM_NIL;
goto LA1;
LA2: ;
Result_59561 = Nextiter_57086(Ti_57084, Tab_57085);
LA1: ;
return Result_59561;
}
N_NIMCALL(NI, Iitablerawget_60157)(TY57223 T_60159, NI Key_60160) {
NI Result_60161;
NI H_60162;
Result_60161 = 0;
H_60162 = 0;
H_60162 = (NI32)(Key_60160 & (T_60159.Data->Sup.len-1));
while (1) {
if (!!((T_60159.Data->data[H_60162].Key == (-2147483647 -1)))) goto LA1;
if (!(T_60159.Data->data[H_60162].Key == Key_60160)) goto LA3;
Result_60161 = H_60162;
goto BeforeRet;
LA3: ;
H_60162 = Nexttry_57213(H_60162, (T_60159.Data->Sup.len-1));
} LA1: ;
Result_60161 = -1;
BeforeRet: ;
return Result_60161;
}
N_NIMCALL(void, Iitablerawinsert_60176)(TY57221** Data_60179, NI Key_60180, NI Val_60181) {
NI H_60182;
H_60182 = 0;
H_60182 = (NI32)(Key_60180 & ((*Data_60179)->Sup.len-1));
while (1) {
if (!!(((*Data_60179)->data[H_60182].Key == (-2147483647 -1)))) goto LA1;
H_60182 = Nexttry_57213(H_60182, ((*Data_60179)->Sup.len-1));
} LA1: ;
(*Data_60179)->data[H_60182].Key = Key_60180;
(*Data_60179)->data[H_60182].Val = Val_60181;
}
N_NIMCALL(void, Iitableput_57236)(TY57223* T_57239, NI Key_57240, NI Val_57241) {
NI Index_60196;
TY57221* N_60197;
NIM_BOOL LOC5;
NI I_60241;
NI HEX3Atmp_60276;
NI Res_60278;
NI I_60249;
NI HEX3Atmp_60282;
NI Res_60284;
TY57221* LOC13;
Index_60196 = 0;
N_60197 = 0;
Index_60196 = Iitablerawget_60157((*T_57239), Key_57240);
if (!(0 <= Index_60196)) goto LA2;
(*T_57239).Data->data[Index_60196].Val = Val_57241;
goto LA1;
LA2: ;
LOC5 = Mustrehash_57209((*T_57239).Data->Sup.len, (*T_57239).Counter);
if (!LOC5) goto LA6;
N_60197 = (TY57221*) newSeq(NTI57221, (NI32)((*T_57239).Data->Sup.len * 2));
I_60241 = 0;
HEX3Atmp_60276 = 0;
HEX3Atmp_60276 = (N_60197->Sup.len-1);
Res_60278 = 0;
Res_60278 = 0;
while (1) {
if (!(Res_60278 <= HEX3Atmp_60276)) goto LA8;
I_60241 = Res_60278;
N_60197->data[I_60241].Key = (-2147483647 -1);
Res_60278 += 1;
} LA8: ;
I_60249 = 0;
HEX3Atmp_60282 = 0;
HEX3Atmp_60282 = ((*T_57239).Data->Sup.len-1);
Res_60284 = 0;
Res_60284 = 0;
while (1) {
if (!(Res_60284 <= HEX3Atmp_60282)) goto LA9;
I_60249 = Res_60284;
if (!!(((*T_57239).Data->data[I_60249].Key == (-2147483647 -1)))) goto LA11;
Iitablerawinsert_60176(&N_60197, (*T_57239).Data->data[I_60249].Key, (*T_57239).Data->data[I_60249].Val);
LA11: ;
Res_60284 += 1;
} LA9: ;
LOC13 = (*T_57239).Data;
unsureAsgnRef((void**) &(*T_57239).Data, N_60197);
N_60197 = LOC13;
LA6: ;
Iitablerawinsert_60176(&(*T_57239).Data, Key_57240, Val_57241);
(*T_57239).Counter += 1;
LA1: ;
}
N_NIMCALL(NI, Idtablerawget_59778)(TY53561 T_59780, NI Key_59781) {
NI Result_59782;
NI H_59783;
Result_59782 = 0;
H_59783 = 0;
H_59783 = (NI32)(Key_59781 & (T_59780.Data->Sup.len-1));
while (1) {
if (!!((T_59780.Data->data[H_59783].Key == NIM_NIL))) goto LA1;
if (!((*T_59780.Data->data[H_59783].Key).Id == Key_59781)) goto LA3;
Result_59782 = H_59783;
goto BeforeRet;
LA3: ;
H_59783 = Nexttry_57213(H_59783, (T_59780.Data->Sup.len-1));
} LA1: ;
Result_59782 = -1;
BeforeRet: ;
return Result_59782;
}
static N_INLINE(void, asgnRefNoCycle)(void** Dest_11616, void* Src_11617) {
TY10402* C_11618;
TY10402* C_11619;
if (!!((Src_11617 == NIM_NIL))) goto LA2;
C_11618 = 0;
C_11618 = Usrtocell_10822(Src_11617);
(*C_11618).Refcount = (NI32)((NU32)((*C_11618).Refcount) + (NU32)(8));
LA2: ;
if (!!(((*Dest_11616) == NIM_NIL))) goto LA5;
C_11619 = 0;
C_11619 = Usrtocell_10822((*Dest_11616));
(*C_11619).Refcount = (NI32)((NU32)((*C_11619).Refcount) - (NU32)(8));
if (!((NU32)((*C_11619).Refcount) < (NU32)(8))) goto LA8;
Rtladdzct_11456(C_11619);
LA8: ;
LA5: ;
(*Dest_11616) = Src_11617;
}
N_NIMCALL(void, Idtablerawinsert_59831)(TY53559** Data_59834, TY52005* Key_59835, TNimObject* Val_59836) {
NI H_59837;
H_59837 = 0;
H_59837 = (NI32)((*Key_59835).Id & ((*Data_59834)->Sup.len-1));
while (1) {
if (!!(((*Data_59834)->data[H_59837].Key == NIM_NIL))) goto LA1;
H_59837 = Nexttry_57213(H_59837, ((*Data_59834)->Sup.len-1));
} LA1: ;
asgnRefNoCycle((void**) &(*Data_59834)->data[H_59837].Key, Key_59835);
asgnRefNoCycle((void**) &(*Data_59834)->data[H_59837].Val, Val_59836);
}
N_NIMCALL(void, Idtableput_57174)(TY53561* T_57177, TY52005* Key_57178, TNimObject* Val_57179) {
NI Index_59869;
TY53559* N_59870;
NIM_BOOL LOC5;
NI I_59923;
NI HEX3Atmp_59959;
NI Res_59961;
TY53559* LOC12;
Index_59869 = 0;
N_59870 = 0;
Index_59869 = Idtablerawget_59778((*T_57177), (*Key_57178).Id);
if (!(0 <= Index_59869)) goto LA2;
asgnRefNoCycle((void**) &(*T_57177).Data->data[Index_59869].Val, Val_57179);
goto LA1;
LA2: ;
LOC5 = Mustrehash_57209((*T_57177).Data->Sup.len, (*T_57177).Counter);
if (!LOC5) goto LA6;
N_59870 = (TY53559*) newSeq(NTI53559, (NI32)((*T_57177).Data->Sup.len * 2));
I_59923 = 0;
HEX3Atmp_59959 = 0;
HEX3Atmp_59959 = ((*T_57177).Data->Sup.len-1);
Res_59961 = 0;
Res_59961 = 0;
while (1) {
if (!(Res_59961 <= HEX3Atmp_59959)) goto LA8;
I_59923 = Res_59961;
if (!!(((*T_57177).Data->data[I_59923].Key == NIM_NIL))) goto LA10;
Idtablerawinsert_59831(&N_59870, (*T_57177).Data->data[I_59923].Key, (*T_57177).Data->data[I_59923].Val);
LA10: ;
Res_59961 += 1;
} LA8: ;
LOC12 = (*T_57177).Data;
unsureAsgnRef((void**) &(*T_57177).Data, N_59870);
N_59870 = LOC12;
LA6: ;
Idtablerawinsert_59831(&(*T_57177).Data, Key_57178, Val_57179);
(*T_57177).Counter += 1;
LA1: ;
}
N_NIMCALL(TNimObject*, Idtableget_57170)(TY53561 T_57172, NI Key_57173) {
TNimObject* Result_59827;
NI Index_59828;
Result_59827 = 0;
Index_59828 = 0;
Index_59828 = Idtablerawget_59778(T_57172, Key_57173);
if (!(0 <= Index_59828)) goto LA2;
Result_59827 = T_57172.Data->data[Index_59828].Val;
goto LA1;
LA2: ;
Result_59827 = NIM_NIL;
LA1: ;
return Result_59827;
}
N_NIMCALL(NI, Iitableget_57232)(TY57223 T_57234, NI Key_57235) {
NI Result_60172;
NI Index_60173;
Result_60172 = 0;
Index_60173 = 0;
Index_60173 = Iitablerawget_60157(T_57234, Key_57235);
if (!(0 <= Index_60173)) goto LA2;
Result_60172 = T_57234.Data->data[Index_60173].Val;
goto LA1;
LA2: ;
Result_60172 = (-2147483647 -1);
LA1: ;
return Result_60172;
}
N_NIMCALL(void, Initsymtab_57111)(TY57107* Tab_57114) {
(*Tab_57114).Tos = 0;
unsureAsgnRef((void**) &(*Tab_57114).Stack, (TY57109*) newSeq(NTI57109, 0));
}
N_NIMCALL(TY53545*, Symtabget_57119)(TY57107 Tab_57121, TY52011* S_57122) {
TY53545* Result_59613;
NI I_59636;
NI HEX3Atmp_59649;
NI Res_59651;
Result_59613 = 0;
I_59636 = 0;
HEX3Atmp_59649 = 0;
HEX3Atmp_59649 = (NI32)(((NI) (Tab_57121.Tos)) - 1);
Res_59651 = 0;
Res_59651 = HEX3Atmp_59649;
while (1) {
if (!(0 <= Res_59651)) goto LA1;
I_59636 = Res_59651;
Result_59613 = Strtableget_57069(&Tab_57121.Stack->data[I_59636], S_57122);
if (!!((Result_59613 == NIM_NIL))) goto LA3;
goto BeforeRet;
LA3: ;
Res_59651 -= 1;
} LA1: ;
Result_59613 = NIM_NIL;
BeforeRet: ;
return Result_59613;
}
N_NIMCALL(TY53545*, Getmodule_57206)(TY53545* S_57208) {
TY53545* Result_57421;
NIM_BOOL LOC2;
Result_57421 = 0;
Result_57421 = S_57208;
while (1) {
LOC2 = !((Result_57421 == NIM_NIL));
if (!(LOC2)) goto LA3;
LOC2 = !(((*Result_57421).Kind == ((NU8) 18)));
LA3: ;
if (!LOC2) goto LA1;
Result_57421 = (*Result_57421).Owner;
} LA1: ;
return Result_57421;
}
N_NIMCALL(TY53545*, Nextidentiter_57101)(TY57092* Ti_57104, TY53527* Tab_57105) {
TY53545* Result_59537;
NI H_59538;
NI Start_59539;
Result_59537 = 0;
H_59538 = 0;
Start_59539 = 0;
H_59538 = (NI32)((*Ti_57104).H & ((*Tab_57105).Data->Sup.len-1));
Start_59539 = H_59538;
Result_59537 = (*Tab_57105).Data->data[H_59538];
while (1) {
if (!!((Result_59537 == NIM_NIL))) goto LA1;
if (!((*(*Result_59537).Name).Sup.Id == (*(*Ti_57104).Name).Sup.Id)) goto LA3;
goto LA1;
LA3: ;
H_59538 = Nexttry_57213(H_59538, ((*Tab_57105).Data->Sup.len-1));
if (!(H_59538 == Start_59539)) goto LA6;
Result_59537 = NIM_NIL;
goto LA1;
LA6: ;
Result_59537 = (*Tab_57105).Data->data[H_59538];
} LA1: ;
(*Ti_57104).H = Nexttry_57213(H_59538, ((*Tab_57105).Data->Sup.len-1));
return Result_59537;
}
N_NIMCALL(TY53545*, Initidentiter_57095)(TY57092* Ti_57098, TY53527* Tab_57099, TY52011* S_57100) {
TY53545* Result_59529;
Result_59529 = 0;
(*Ti_57098).H = (*S_57100).H;
unsureAsgnRef((void**) &(*Ti_57098).Name, S_57100);
if (!((*Tab_57099).Counter == 0)) goto LA2;
Result_59529 = NIM_NIL;
goto LA1;
LA2: ;
Result_59529 = Nextidentiter_57101(Ti_57098, Tab_57099);
LA1: ;
return Result_59529;
}
N_NIMCALL(NI, Idnodetablerawget_59967)(TY53567 T_59969, TY52005* Key_59970) {
NI Result_59971;
NI H_59972;
Result_59971 = 0;
H_59972 = 0;
H_59972 = (NI32)((*Key_59970).Id & (T_59969.Data->Sup.len-1));
while (1) {
if (!!((T_59969.Data->data[H_59972].Key == NIM_NIL))) goto LA1;
if (!((*T_59969.Data->data[H_59972].Key).Id == (*Key_59970).Id)) goto LA3;
Result_59971 = H_59972;
goto BeforeRet;
LA3: ;
H_59972 = Nexttry_57213(H_59972, (T_59969.Data->Sup.len-1));
} LA1: ;
Result_59971 = -1;
BeforeRet: ;
return Result_59971;
}
N_NIMCALL(TY53523*, Idnodetableget_57184)(TY53567 T_57186, TY52005* Key_57187) {
TY53523* Result_59991;
NI Index_59992;
Result_59991 = 0;
Index_59992 = 0;
Index_59992 = Idnodetablerawget_59967(T_57186, Key_57187);
if (!(0 <= Index_59992)) goto LA2;
Result_59991 = T_57186.Data->data[Index_59992].Val;
goto LA1;
LA2: ;
Result_59991 = NIM_NIL;
LA1: ;
return Result_59991;
}
N_NIMCALL(void, Idnodetablerawinsert_59995)(TY53565** Data_59998, TY52005* Key_59999, TY53523* Val_60000) {
NI H_60001;
H_60001 = 0;
H_60001 = (NI32)((*Key_59999).Id & ((*Data_59998)->Sup.len-1));
while (1) {
if (!!(((*Data_59998)->data[H_60001].Key == NIM_NIL))) goto LA1;
H_60001 = Nexttry_57213(H_60001, ((*Data_59998)->Sup.len-1));
} LA1: ;
asgnRefNoCycle((void**) &(*Data_59998)->data[H_60001].Key, Key_59999);
asgnRefNoCycle((void**) &(*Data_59998)->data[H_60001].Val, Val_60000);
}
N_NIMCALL(void, Idnodetableput_57188)(TY53567* T_57191, TY52005* Key_57192, TY53523* Val_57193) {
NI Index_60033;
TY53565* N_60034;
NIM_BOOL LOC5;
NI I_60087;
NI HEX3Atmp_60123;
NI Res_60125;
TY53565* LOC12;
Index_60033 = 0;
N_60034 = 0;
Index_60033 = Idnodetablerawget_59967((*T_57191), Key_57192);
if (!(0 <= Index_60033)) goto LA2;
asgnRefNoCycle((void**) &(*T_57191).Data->data[Index_60033].Val, Val_57193);
goto LA1;
LA2: ;
LOC5 = Mustrehash_57209((*T_57191).Data->Sup.len, (*T_57191).Counter);
if (!LOC5) goto LA6;
N_60034 = (TY53565*) newSeq(NTI53565, (NI32)((*T_57191).Data->Sup.len * 2));
I_60087 = 0;
HEX3Atmp_60123 = 0;
HEX3Atmp_60123 = ((*T_57191).Data->Sup.len-1);
Res_60125 = 0;
Res_60125 = 0;
while (1) {
if (!(Res_60125 <= HEX3Atmp_60123)) goto LA8;
I_60087 = Res_60125;
if (!!(((*T_57191).Data->data[I_60087].Key == NIM_NIL))) goto LA10;
Idnodetablerawinsert_59995(&N_60034, (*T_57191).Data->data[I_60087].Key, (*T_57191).Data->data[I_60087].Val);
LA10: ;
Res_60125 += 1;
} LA8: ;
LOC12 = (*T_57191).Data;
unsureAsgnRef((void**) &(*T_57191).Data, N_60034);
N_60034 = LOC12;
LA6: ;
Idnodetablerawinsert_59995(&(*T_57191).Data, Key_57192, Val_57193);
(*T_57191).Counter += 1;
LA1: ;
}
N_NIMCALL(TY53545*, Getsymfromlist_57197)(TY53523* List_57199, TY52011* Ident_57200, NI Start_57201) {
TY53545* Result_57466;
NI I_57474;
NI HEX3Atmp_57523;
NI LOC1;
NI Res_57525;
Result_57466 = 0;
I_57474 = 0;
HEX3Atmp_57523 = 0;
LOC1 = Sonslen_53801(List_57199);
HEX3Atmp_57523 = (NI32)(LOC1 - 1);
Res_57525 = 0;
Res_57525 = Start_57201;
while (1) {
if (!(Res_57525 <= HEX3Atmp_57523)) goto LA2;
I_57474 = Res_57525;
if (!!(((*(*List_57199).KindU.S6.Sons->data[I_57474]).Kind == ((NU8) 3)))) goto LA4;
Internalerror_45567((*List_57199).Info, ((NimStringDesc*) &TMP194056));
LA4: ;
Result_57466 = (*(*List_57199).KindU.S6.Sons->data[I_57474]).KindU.S4.Sym;
if (!((*(*Result_57466).Name).Sup.Id == (*Ident_57200).Sup.Id)) goto LA7;
goto BeforeRet;
LA7: ;
Res_57525 += 1;
} LA2: ;
Result_57466 = NIM_NIL;
BeforeRet: ;
return Result_57466;
}
N_NIMCALL(TNimObject*, Idtableget_57166)(TY53561 T_57168, TY52005* Key_57169) {
TNimObject* Result_59819;
NI Index_59820;
Result_59819 = 0;
Index_59820 = 0;
Index_59820 = Idtablerawget_59778(T_57168, (*Key_57169).Id);
if (!(0 <= Index_59820)) goto LA2;
Result_59819 = T_57168.Data->data[Index_59820].Val;
goto LA1;
LA2: ;
Result_59819 = NIM_NIL;
LA1: ;
return Result_59819;
}
N_NIMCALL(void, Openscope_57149)(TY57107* Tab_57152) {
if (!((*Tab_57152).Stack->Sup.len <= ((NI) ((*Tab_57152).Tos)))) goto LA2;
(*Tab_57152).Stack = (TY57109*) setLengthSeq(&((*Tab_57152).Stack)->Sup, sizeof(TY53527), (NI32)(((NI) ((*Tab_57152).Tos)) + 1));
LA2: ;
Initstrtable_53744(&(*Tab_57152).Stack->data[(*Tab_57152).Tos]);
(*Tab_57152).Tos += 1;
}
N_NIMCALL(NU8, Symtabadduniqueat_57143)(TY57107* Tab_57146, TY53545* E_57147, NI At_57148) {
NU8 Result_59673;
TY53545* LOC2;
Result_59673 = 0;
LOC2 = Strtableget_57069(&(*Tab_57146).Stack->data[At_57148], (*E_57147).Name);
if (!!((LOC2 == NIM_NIL))) goto LA3;
Result_59673 = ((NU8) 0);
goto LA1;
LA3: ;
Strtableadd_57064(&(*Tab_57146).Stack->data[At_57148], E_57147);
Result_59673 = ((NU8) 1);
LA1: ;
return Result_59673;
}
N_NIMCALL(NU8, Symtabaddunique_57138)(TY57107* Tab_57141, TY53545* E_57142) {
NU8 Result_59691;
Result_59691 = 0;
Result_59691 = Symtabadduniqueat_57143(Tab_57141, E_57142, ((NI) ((NI32)(((NI) ((*Tab_57141).Tos)) - 1))));
return Result_59691;
}
N_NIMCALL(void, Rawclosescope_57153)(TY57107* Tab_57156) {
(*Tab_57156).Tos -= 1;
}
N_NIMCALL(TY50008*, Debugtype_58411)(TY53549* N_58413) {
TY50008* Result_58414;
NIM_BOOL LOC8;
NI LOC10;
NI I_58466;
NI HEX3Atmp_58485;
NI LOC13;
NI Res_58487;
TY50008* LOC21;
Result_58414 = 0;
if (!(N_58413 == NIM_NIL)) goto LA2;
Result_58414 = Torope_50046(((NimStringDesc*) &TMP194138));
goto LA1;
LA2: ;
Result_58414 = Torope_50046(reprEnum((*N_58413).Kind, NTI53162));
if (!!(((*N_58413).Sym == NIM_NIL))) goto LA5;
App_50036(&Result_58414, ((NimStringDesc*) &TMP194139));
App_50036(&Result_58414, (*(*(*N_58413).Sym).Name).S);
LA5: ;
LOC8 = !(((*N_58413).Kind == ((NU8) 28)));
if (!(LOC8)) goto LA9;
LOC10 = Sonslen_53804(N_58413);
LOC8 = (0 < LOC10);
LA9: ;
if (!LOC8) goto LA11;
App_50036(&Result_58414, ((NimStringDesc*) &TMP194140));
I_58466 = 0;
HEX3Atmp_58485 = 0;
LOC13 = Sonslen_53804(N_58413);
HEX3Atmp_58485 = (NI32)(LOC13 - 1);
Res_58487 = 0;
Res_58487 = 0;
while (1) {
if (!(Res_58487 <= HEX3Atmp_58485)) goto LA14;
I_58466 = Res_58487;
if (!(0 < I_58466)) goto LA16;
App_50036(&Result_58414, ((NimStringDesc*) &TMP194141));
LA16: ;
if (!((*N_58413).Sons->data[I_58466] == NIM_NIL)) goto LA19;
App_50036(&Result_58414, ((NimStringDesc*) &TMP194138));
goto LA18;
LA19: ;
LOC21 = Debugtype_58411((*N_58413).Sons->data[I_58466]);
App_50031(&Result_58414, LOC21);
LA18: ;
Res_58487 += 1;
} LA14: ;
App_50036(&Result_58414, ((NimStringDesc*) &TMP194142));
LA11: ;
LA1: ;
return Result_58414;
}
N_NIMCALL(void, Debug_57160)(TY53549* N_57162) {
TY50008* LOC1;
NimStringDesc* LOC2;
LOC1 = Debugtype_58411(N_57162);
LOC2 = Ropetostr_50066(LOC1);
Writeln_58812(stdout, LOC2);
}
N_NIMCALL(void, Symtabaddat_57132)(TY57107* Tab_57135, TY53545* E_57136, NI At_57137) {
Strtableadd_57064(&(*Tab_57135).Stack->data[At_57137], E_57136);
}
N_NIMCALL(TY53545*, Symtablocalget_57123)(TY57107 Tab_57125, TY52011* S_57126) {
TY53545* Result_59608;
Result_59608 = 0;
Result_59608 = Strtableget_57069(&Tab_57125.Stack->data[(NI32)(((NI) (Tab_57125.Tos)) - 1)], S_57126);
return Result_59608;
}
N_NIMCALL(void, Symtabadd_57127)(TY57107* Tab_57130, TY53545* E_57131) {
Strtableadd_57064(&(*Tab_57130).Stack->data[(NI32)(((NI) ((*Tab_57130).Tos)) - 1)], E_57131);
}
N_NIMCALL(NIM_BOOL, Idtablehasobjectaskey_57180)(TY53561 T_57182, TY52005* Key_57183) {
NIM_BOOL Result_59802;
NI Index_59803;
Result_59802 = 0;
Index_59803 = 0;
Index_59803 = Idtablerawget_59778(T_57182, (*Key_57183).Id);
if (!(0 <= Index_59803)) goto LA2;
Result_59802 = (T_57182.Data->data[Index_59803].Key == Key_57183);
goto LA1;
LA2: ;
Result_59802 = NIM_FALSE;
LA1: ;
return Result_59802;
}
N_NIMCALL(TY53545*, Lookupinrecord_57202)(TY53523* N_57204, TY52011* Field_57205) {
TY53545* Result_57246;
NI I_57269;
NI HEX3Atmp_57407;
NI LOC1;
NI Res_57409;
NI I_57344;
NI HEX3Atmp_57413;
NI LOC12;
NI Res_57415;
TY53523* LOC14;
Result_57246 = 0;
Result_57246 = NIM_NIL;
switch ((*N_57204).Kind) {
case ((NU8) 113):
I_57269 = 0;
HEX3Atmp_57407 = 0;
LOC1 = Sonslen_53801(N_57204);
HEX3Atmp_57407 = (NI32)(LOC1 - 1);
Res_57409 = 0;
Res_57409 = 0;
while (1) {
if (!(Res_57409 <= HEX3Atmp_57407)) goto LA2;
I_57269 = Res_57409;
Result_57246 = Lookupinrecord_57202((*N_57204).KindU.S6.Sons->data[I_57269], Field_57205);
if (!!((Result_57246 == NIM_NIL))) goto LA4;
goto BeforeRet;
LA4: ;
Res_57409 += 1;
} LA2: ;
break;
case ((NU8) 114):
if (!!(((*(*N_57204).KindU.S6.Sons->data[0]).Kind == ((NU8) 3)))) goto LA7;
Internalerror_45567((*N_57204).Info, ((NimStringDesc*) &TMP194681));
LA7: ;
Result_57246 = Lookupinrecord_57202((*N_57204).KindU.S6.Sons->data[0], Field_57205);
if (!!((Result_57246 == NIM_NIL))) goto LA10;
goto BeforeRet;
LA10: ;
I_57344 = 0;
HEX3Atmp_57413 = 0;
LOC12 = Sonslen_53801(N_57204);
HEX3Atmp_57413 = (NI32)(LOC12 - 1);
Res_57415 = 0;
Res_57415 = 1;
while (1) {
if (!(Res_57415 <= HEX3Atmp_57413)) goto LA13;
I_57344 = Res_57415;
switch ((*(*N_57204).KindU.S6.Sons->data[I_57344]).Kind) {
case ((NU8) 75):
case ((NU8) 78):
LOC14 = Lastson_53807((*N_57204).KindU.S6.Sons->data[I_57344]);
Result_57246 = Lookupinrecord_57202(LOC14, Field_57205);
if (!!((Result_57246 == NIM_NIL))) goto LA16;
goto BeforeRet;
LA16: ;
break;
default:
Internalerror_45567((*N_57204).Info, ((NimStringDesc*) &TMP194682));
break;
}
Res_57415 += 1;
} LA13: ;
break;
case ((NU8) 3):
if (!((*(*(*N_57204).KindU.S4.Sym).Name).Sup.Id == (*Field_57205).Sup.Id)) goto LA19;
Result_57246 = (*N_57204).KindU.S4.Sym;
LA19: ;
break;
default:
Internalerror_45567((*N_57204).Info, ((NimStringDesc*) &TMP194683));
break;
}
BeforeRet: ;
return Result_57246;
}
N_NIMCALL(void, Writeln_58812)(FILE* F_58815, NimStringDesc* X_58816) {
Write_3658(F_58815, X_58816);
Write_3658(F_58815, ((NimStringDesc*) &TMP195493));
}
N_NOINLINE(void, astalgoInit)(void) {
}
