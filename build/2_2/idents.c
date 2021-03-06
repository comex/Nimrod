/* Generated by Nimrod Compiler v0.8.9 */
/*   (c) 2010 Andreas Rumpf */

typedef long long int NI;
typedef unsigned long long int NU;
#include "nimbase.h"

#include <pthread.h>
typedef struct TY53011 TY53011;
typedef struct NimStringDesc NimStringDesc;
typedef struct TGenericSeq TGenericSeq;
typedef struct TY53005 TY53005;
typedef struct TNimObject TNimObject;
typedef struct TNimType TNimType;
typedef struct TNimNode TNimNode;
typedef struct TY10802 TY10802;
typedef struct TY11190 TY11190;
typedef struct TY10818 TY10818;
typedef struct TY10814 TY10814;
typedef struct TY10810 TY10810;
typedef struct TY11188 TY11188;
struct TGenericSeq {
NI len;
NI space;
};
typedef NIM_CHAR TY239[100000001];
struct NimStringDesc {
  TGenericSeq Sup;
TY239 data;
};
struct TNimType {
NI size;
NU8 kind;
NU8 flags;
TNimType* base;
TNimNode* node;
void* finalizer;
};
struct TNimObject {
TNimType* m_type;
};
struct TY53005 {
  TNimObject Sup;
NI Id;
};
struct TY53011 {
  TY53005 Sup;
NimStringDesc* S;
TY53011* Next;
NI H;
};
typedef TY53011* TY53039[8192];
struct TY10802 {
NI Refcount;
TNimType* Typ;
};
struct TY10818 {
NI Len;
NI Cap;
TY10802** D;
};
struct TY10814 {
NI Counter;
NI Max;
TY10810* Head;
TY10810** Data;
};
struct TY11188 {
NI Stackscans;
NI Cyclecollections;
NI Maxthreshold;
NI Maxstacksize;
NI Maxstackcells;
NI Cycletablesize;
};
struct TY11190 {
TY10818 Zct;
TY10818 Decstack;
TY10814 Cycleroots;
TY10818 Tempstack;
NI Cyclerootslock;
NI Zctlock;
TY11188 Stat;
};
struct TNimNode {
NU8 kind;
NI offset;
TNimType* typ;
NCSTRING name;
NI len;
TNimNode** sons;
};
typedef NI TY8814[8];
struct TY10810 {
TY10810* Next;
NI Key;
TY8814 Bits;
};
N_NIMCALL(NIM_BOOL, Identeq_53028)(TY53011* Id_53030, NimStringDesc* Name_53031);
N_NIMCALL(NI, Cmpignorestyle_53042)(NCSTRING A_53044, NCSTRING B_53045, NI Blen_53046);
static N_INLINE(NI, addInt)(NI A_5803, NI B_5804);
N_NOINLINE(void, raiseOverflow)(void);
static N_INLINE(NI, subInt)(NI A_6003, NI B_6004);
N_NIMCALL(NI, Cmpexact_53165)(NCSTRING A_53167, NCSTRING B_53168, NI Blen_53169);
N_NIMCALL(TY53011*, Getident_53016)(NimStringDesc* Identifier_53018);
N_NIMCALL(NI, Getnormalizedhash_43037)(NimStringDesc* S_43039);
N_NIMCALL(TY53011*, Getident_53019)(NimStringDesc* Identifier_53021, NI H_53022);
N_NIMCALL(TY53011*, Getident_53023)(NCSTRING Identifier_53025, NI Length_53026, NI H_53027);
N_NOINLINE(void, raiseIndexError)(void);
static N_INLINE(void, asgnRefNoCycle)(void** Dest_12018, void* Src_12019);
static N_INLINE(TY10802*, Usrtocell_11236)(void* Usr_11238);
static N_INLINE(NI, Atomicinc_3001)(NI* Memloc_3004, NI X_3005);
static N_INLINE(NI, Atomicdec_3006)(NI* Memloc_3009, NI X_3010);
static N_INLINE(void, Rtladdzct_11858)(TY10802* C_11860);
N_NOINLINE(void, Addzct_11225)(TY10818* S_11228, TY10802* C_11229);
N_NIMCALL(void, internalAssert)(NCSTRING File_5254, NI Line_5255, NIM_BOOL Cond_5256);
N_NIMCALL(void*, newObj)(TNimType* Typ_12507, NI Size_12508);
N_NIMCALL(NimStringDesc*, mnewString)(NI Len_1349);
TY53039 Buckets_53041;
NI Wordcounter_53233;
extern TY11190 Gch_11210;
extern TNimType* NTI53009; /* PIdent */
extern TNimType* NTI53011; /* TIdent */
N_NIMCALL(NIM_BOOL, Identeq_53028)(TY53011* Id_53030, NimStringDesc* Name_53031) {
NIM_BOOL Result_53036;
TY53011* LOC1;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "IdentEq";
F.prev = framePtr;
F.filename = "rod/idents.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_53036 = 0;
F.line = 38;F.filename = "idents.nim";
LOC1 = 0;
LOC1 = Getident_53016(Name_53031);
Result_53036 = ((*Id_53030).Sup.Id == (*LOC1).Sup.Id);
framePtr = framePtr->prev;
return Result_53036;
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
static N_INLINE(NI, subInt)(NI A_6003, NI B_6004) {
NI Result_6005;
NIM_BOOL LOC2;
Result_6005 = 0;
Result_6005 = (NI64)((NU64)(A_6003) - (NU64)(B_6004));
LOC2 = (0 <= (NI64)(Result_6005 ^ A_6003));
if (LOC2) goto LA3;
LOC2 = (0 <= (NI64)(Result_6005 ^ (NI64)((NU64) ~(B_6004))));
LA3: ;
if (!LOC2) goto LA4;
goto BeforeRet;
LA4: ;
raiseOverflow();
BeforeRet: ;
return Result_6005;
}
N_NIMCALL(NI, Cmpignorestyle_53042)(NCSTRING A_53044, NCSTRING B_53045, NI Blen_53046) {
NI Result_53047;
NIM_CHAR Aa_53048;
NIM_CHAR Bb_53049;
NI I_53050;
NI J_53051;
NIM_BOOL LOC5;
NIM_BOOL LOC10;
NIM_BOOL LOC15;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "cmpIgnoreStyle";
F.prev = framePtr;
F.filename = "rod/idents.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_53047 = 0;
Aa_53048 = 0;
Bb_53049 = 0;
I_53050 = 0;
J_53051 = 0;
F.line = 46;F.filename = "idents.nim";
I_53050 = 0;
F.line = 47;F.filename = "idents.nim";
J_53051 = 0;
F.line = 48;F.filename = "idents.nim";
Result_53047 = 1;
F.line = 49;F.filename = "idents.nim";
while (1) {
if (!(J_53051 < Blen_53046)) goto LA1;
F.line = 50;F.filename = "idents.nim";
while (1) {
if (!((NU8)(A_53044[I_53050]) == (NU8)(95))) goto LA2;
F.line = 50;F.filename = "idents.nim";
I_53050 = addInt(I_53050, 1);
} LA2: ;
F.line = 51;F.filename = "idents.nim";
while (1) {
if (!((NU8)(B_53045[J_53051]) == (NU8)(95))) goto LA3;
F.line = 52;F.filename = "idents.nim";
J_53051 = addInt(J_53051, 1);
} LA3: ;
F.line = 53;F.filename = "idents.nim";
Aa_53048 = A_53044[I_53050];
F.line = 54;F.filename = "idents.nim";
Bb_53049 = B_53045[J_53051];
F.line = 55;F.filename = "idents.nim";
LOC5 = ((NU8)(65) <= (NU8)(Aa_53048));
if (!(LOC5)) goto LA6;
LOC5 = ((NU8)(Aa_53048) <= (NU8)(90));
LA6: ;
if (!LOC5) goto LA7;
F.line = 55;F.filename = "idents.nim";
Aa_53048 = ((NIM_CHAR) (((NI) (addInt(((NU8)(Aa_53048)), 32)))));
LA7: ;
F.line = 56;F.filename = "idents.nim";
LOC10 = ((NU8)(65) <= (NU8)(Bb_53049));
if (!(LOC10)) goto LA11;
LOC10 = ((NU8)(Bb_53049) <= (NU8)(90));
LA11: ;
if (!LOC10) goto LA12;
F.line = 56;F.filename = "idents.nim";
Bb_53049 = ((NIM_CHAR) (((NI) (addInt(((NU8)(Bb_53049)), 32)))));
LA12: ;
F.line = 57;F.filename = "idents.nim";
Result_53047 = subInt(((NU8)(Aa_53048)), ((NU8)(Bb_53049)));
F.line = 58;F.filename = "idents.nim";
LOC15 = !((Result_53047 == 0));
if (LOC15) goto LA16;
LOC15 = ((NU8)(Aa_53048) == (NU8)(0));
LA16: ;
if (!LOC15) goto LA17;
F.line = 58;F.filename = "idents.nim";
goto LA1;
LA17: ;
F.line = 59;F.filename = "idents.nim";
I_53050 = addInt(I_53050, 1);
F.line = 60;F.filename = "idents.nim";
J_53051 = addInt(J_53051, 1);
} LA1: ;
F.line = 61;F.filename = "idents.nim";
if (!(Result_53047 == 0)) goto LA20;
F.line = 62;F.filename = "idents.nim";
if (!!(((NU8)(A_53044[I_53050]) == (NU8)(0)))) goto LA23;
F.line = 62;F.filename = "idents.nim";
Result_53047 = 1;
LA23: ;
LA20: ;
framePtr = framePtr->prev;
return Result_53047;
}
N_NIMCALL(NI, Cmpexact_53165)(NCSTRING A_53167, NCSTRING B_53168, NI Blen_53169) {
NI Result_53170;
NIM_CHAR Aa_53171;
NIM_CHAR Bb_53172;
NI I_53173;
NI J_53174;
NIM_BOOL LOC3;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "cmpExact";
F.prev = framePtr;
F.filename = "rod/idents.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_53170 = 0;
Aa_53171 = 0;
Bb_53172 = 0;
I_53173 = 0;
J_53174 = 0;
F.line = 68;F.filename = "idents.nim";
I_53173 = 0;
F.line = 69;F.filename = "idents.nim";
J_53174 = 0;
F.line = 70;F.filename = "idents.nim";
Result_53170 = 1;
F.line = 71;F.filename = "idents.nim";
while (1) {
if (!(J_53174 < Blen_53169)) goto LA1;
F.line = 72;F.filename = "idents.nim";
Aa_53171 = A_53167[I_53173];
F.line = 73;F.filename = "idents.nim";
Bb_53172 = B_53168[J_53174];
F.line = 74;F.filename = "idents.nim";
Result_53170 = subInt(((NU8)(Aa_53171)), ((NU8)(Bb_53172)));
F.line = 75;F.filename = "idents.nim";
LOC3 = !((Result_53170 == 0));
if (LOC3) goto LA4;
LOC3 = ((NU8)(Aa_53171) == (NU8)(0));
LA4: ;
if (!LOC3) goto LA5;
F.line = 75;F.filename = "idents.nim";
goto LA1;
LA5: ;
F.line = 76;F.filename = "idents.nim";
I_53173 = addInt(I_53173, 1);
F.line = 77;F.filename = "idents.nim";
J_53174 = addInt(J_53174, 1);
} LA1: ;
F.line = 78;F.filename = "idents.nim";
if (!(Result_53170 == 0)) goto LA8;
F.line = 79;F.filename = "idents.nim";
if (!!(((NU8)(A_53167[I_53173]) == (NU8)(0)))) goto LA11;
F.line = 79;F.filename = "idents.nim";
Result_53170 = 1;
LA11: ;
LA8: ;
framePtr = framePtr->prev;
return Result_53170;
}
N_NIMCALL(TY53011*, Getident_53016)(NimStringDesc* Identifier_53018) {
TY53011* Result_53223;
NI LOC1;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "getIdent";
F.prev = framePtr;
F.filename = "rod/idents.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_53223 = 0;
F.line = 82;F.filename = "idents.nim";
LOC1 = Getnormalizedhash_43037(Identifier_53018);
Result_53223 = Getident_53023(Identifier_53018->data, Identifier_53018->Sup.len, LOC1);
framePtr = framePtr->prev;
return Result_53223;
}
N_NIMCALL(TY53011*, Getident_53019)(NimStringDesc* Identifier_53021, NI H_53022) {
TY53011* Result_53230;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "getIdent";
F.prev = framePtr;
F.filename = "rod/idents.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_53230 = 0;
F.line = 86;F.filename = "idents.nim";
Result_53230 = Getident_53023(Identifier_53021->data, Identifier_53021->Sup.len, H_53022);
framePtr = framePtr->prev;
return Result_53230;
}
static N_INLINE(TY10802*, Usrtocell_11236)(void* Usr_11238) {
TY10802* Result_11239;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "usrToCell";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/gc.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_11239 = 0;
F.line = 100;F.filename = "gc.nim";
Result_11239 = ((TY10802*) ((NI64)((NU64)(((NI) (Usr_11238))) - (NU64)(((NI) (((NI)sizeof(TY10802))))))));
framePtr = framePtr->prev;
return Result_11239;
}
static N_INLINE(NI, Atomicinc_3001)(NI* Memloc_3004, NI X_3005) {
NI Result_7408;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "atomicInc";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/systhread.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_7408 = 0;
F.line = 29;F.filename = "systhread.nim";
Result_7408 = __sync_add_and_fetch(Memloc_3004, X_3005);
framePtr = framePtr->prev;
return Result_7408;
}
static N_INLINE(NI, Atomicdec_3006)(NI* Memloc_3009, NI X_3010) {
NI Result_7606;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "atomicDec";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/systhread.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_7606 = 0;
F.line = 37;F.filename = "systhread.nim";
Result_7606 = __sync_sub_and_fetch(Memloc_3009, X_3010);
framePtr = framePtr->prev;
return Result_7606;
}
static N_INLINE(void, Rtladdzct_11858)(TY10802* C_11860) {
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "rtlAddZCT";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/gc.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 211;F.filename = "gc.nim";
if (!NIM_TRUE) goto LA2;
F.line = 211;F.filename = "gc.nim";
pthread_mutex_lock(&Gch_11210.Zctlock);
LA2: ;
F.line = 212;F.filename = "gc.nim";
Addzct_11225(&Gch_11210.Zct, C_11860);
F.line = 213;F.filename = "gc.nim";
if (!NIM_TRUE) goto LA5;
F.line = 213;F.filename = "gc.nim";
pthread_mutex_unlock(&Gch_11210.Zctlock);
LA5: ;
framePtr = framePtr->prev;
}
static N_INLINE(void, asgnRefNoCycle)(void** Dest_12018, void* Src_12019) {
TY10802* C_12020;
NI LOC4;
TY10802* C_12022;
NI LOC9;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "asgnRefNoCycle";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/gc.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 244;F.filename = "gc.nim";
if (!!((Src_12019 == NIM_NIL))) goto LA2;
C_12020 = 0;
F.line = 245;F.filename = "gc.nim";
C_12020 = Usrtocell_11236(Src_12019);
F.line = 246;F.filename = "gc.nim";
LOC4 = Atomicinc_3001(&(*C_12020).Refcount, 8);
LA2: ;
F.line = 247;F.filename = "gc.nim";
if (!!(((*Dest_12018) == NIM_NIL))) goto LA6;
C_12022 = 0;
F.line = 248;F.filename = "gc.nim";
C_12022 = Usrtocell_11236((*Dest_12018));
F.line = 249;F.filename = "gc.nim";
LOC9 = Atomicdec_3006(&(*C_12022).Refcount, 8);
if (!((NU64)(LOC9) < (NU64)(8))) goto LA10;
F.line = 250;F.filename = "gc.nim";
Rtladdzct_11858(C_12022);
LA10: ;
LA6: ;
F.line = 251;F.filename = "gc.nim";
(*Dest_12018) = Src_12019;
framePtr = framePtr->prev;
}
N_NIMCALL(TY53011*, Getident_53023)(NCSTRING Identifier_53025, NI Length_53026, NI H_53027) {
TY53011* Result_53239;
NI Idx_53240;
NI Id_53241;
TY53011* Last_53242;
NI LOC3;
NI LOC9;
NIM_BOOL LOC12;
NI I_53310;
NI HEX3Atmp_53327;
NI Res_53329;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "getIdent";
F.prev = framePtr;
F.filename = "rod/idents.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_53239 = 0;
Idx_53240 = 0;
Id_53241 = 0;
Last_53242 = 0;
F.line = 94;F.filename = "idents.nim";
Idx_53240 = (NI64)(H_53027 & 8191);
F.line = 95;F.filename = "idents.nim";
if ((NU)(Idx_53240) > (NU)(8191)) raiseIndexError();
Result_53239 = Buckets_53041[(Idx_53240)-0];
F.line = 96;F.filename = "idents.nim";
Last_53242 = NIM_NIL;
F.line = 97;F.filename = "idents.nim";
Id_53241 = 0;
F.line = 98;F.filename = "idents.nim";
while (1) {
if (!!((Result_53239 == NIM_NIL))) goto LA1;
F.line = 99;F.filename = "idents.nim";
LOC3 = Cmpexact_53165((*Result_53239).S->data, Identifier_53025, Length_53026);
if (!(LOC3 == 0)) goto LA4;
F.line = 100;F.filename = "idents.nim";
if (!!((Last_53242 == NIM_NIL))) goto LA7;
F.line = 102;F.filename = "idents.nim";
asgnRefNoCycle((void**) &(*Last_53242).Next, (*Result_53239).Next);
F.line = 103;F.filename = "idents.nim";
if ((NU)(Idx_53240) > (NU)(8191)) raiseIndexError();
asgnRefNoCycle((void**) &(*Result_53239).Next, Buckets_53041[(Idx_53240)-0]);
F.line = 104;F.filename = "idents.nim";
if ((NU)(Idx_53240) > (NU)(8191)) raiseIndexError();
asgnRefNoCycle((void**) &Buckets_53041[(Idx_53240)-0], Result_53239);
LA7: ;
F.line = 105;F.filename = "idents.nim";
goto BeforeRet;
goto LA2;
LA4: ;
LOC9 = Cmpignorestyle_53042((*Result_53239).S->data, Identifier_53025, Length_53026);
if (!(LOC9 == 0)) goto LA10;
F.line = 117;F.filename = "idents.nim";
LOC12 = (Id_53241 == 0);
if (LOC12) goto LA13;
LOC12 = (Id_53241 == (*Result_53239).Sup.Id);
LA13: ;
internalAssert("rod/idents.nim", 117, LOC12);
F.line = 118;F.filename = "idents.nim";
Id_53241 = (*Result_53239).Sup.Id;
goto LA2;
LA10: ;
LA2: ;
F.line = 119;F.filename = "idents.nim";
Last_53242 = Result_53239;
F.line = 120;F.filename = "idents.nim";
Result_53239 = (*Result_53239).Next;
} LA1: ;
F.line = 121;F.filename = "idents.nim";
Result_53239 = (TY53011*) newObj(NTI53009, sizeof(TY53011));
(*Result_53239).Sup.Sup.m_type = NTI53011;
F.line = 122;F.filename = "idents.nim";
(*Result_53239).H = H_53027;
F.line = 123;F.filename = "idents.nim";
asgnRefNoCycle((void**) &(*Result_53239).S, mnewString(Length_53026));
I_53310 = 0;
HEX3Atmp_53327 = 0;
F.line = 124;F.filename = "idents.nim";
HEX3Atmp_53327 = subInt(addInt(Length_53026, 0), 1);
Res_53329 = 0;
F.line = 1021;F.filename = "system.nim";
Res_53329 = 0;
F.line = 1022;F.filename = "system.nim";
while (1) {
if (!(Res_53329 <= HEX3Atmp_53327)) goto LA14;
F.line = 1021;F.filename = "system.nim";
I_53310 = Res_53329;
F.line = 124;F.filename = "idents.nim";
if ((NU)(I_53310) > (NU)((*Result_53239).S->Sup.len)) raiseIndexError();
(*Result_53239).S->data[I_53310] = Identifier_53025[subInt(I_53310, 0)];
F.line = 1024;F.filename = "system.nim";
Res_53329 = addInt(Res_53329, 1);
} LA14: ;
F.line = 125;F.filename = "idents.nim";
if ((NU)(Idx_53240) > (NU)(8191)) raiseIndexError();
asgnRefNoCycle((void**) &(*Result_53239).Next, Buckets_53041[(Idx_53240)-0]);
F.line = 126;F.filename = "idents.nim";
if ((NU)(Idx_53240) > (NU)(8191)) raiseIndexError();
asgnRefNoCycle((void**) &Buckets_53041[(Idx_53240)-0], Result_53239);
F.line = 127;F.filename = "idents.nim";
if (!(Id_53241 == 0)) goto LA16;
F.line = 128;F.filename = "idents.nim";
Wordcounter_53233 = addInt(Wordcounter_53233, 1);
F.line = 129;F.filename = "idents.nim";
if (Wordcounter_53233 == (IL64(-9223372036854775807) - IL64(1))) raiseOverflow();
(*Result_53239).Sup.Id = ((NI64)-(Wordcounter_53233));
goto LA15;
LA16: ;
F.line = 131;F.filename = "idents.nim";
(*Result_53239).Sup.Id = Id_53241;
LA15: ;
BeforeRet: ;
framePtr = framePtr->prev;
return Result_53239;
}
N_NOINLINE(void, identsInit)(void) {
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "idents";
F.prev = framePtr;
F.filename = "rod/idents.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 88;F.filename = "idents.nim";
Wordcounter_53233 = 1;
framePtr = framePtr->prev;
}

