$Title Simultaneous Optimization for HEN Synthesis

$Ontext

Reference:

1. Yee, T F, and Grossmann, I E, Simultaneous Optimization of Models for
Heat Integration - Heat Exchanger Network Synthesis. Computers and
Chemical Engineering 14, 10 (1990), 1151-1184.

2. J. J. J. Chen. Comments on improvements on a replacement for the logarithmic
mean, Chem. Eng. Sci., 1987, 42:2488.

Adapated by Zhichao Chen(AKA Justus) from Sun Yat-sen University& Zhejiang University

$Offtext

*==============================================================================
* Set Definition:
*==============================================================================

sets
i hot streams /H1,H2,H3,H4,H5/

j cold streams /C1,C2,C3,C4,C5/
HotU  "Hot Uitlity"  /HU1*HU2/
ColdU "Cold Utility" /CU1*CU2/
;

scalar nok  number of stages in superstructure / 5 /;

set
k          temperature locations  nok + 1 /1*6/
st(k)      stages k
first(k)   first temperature location
last(k)    last temperature location

;


st(k)    = yes$(ord(k) lt card(k))  ;
first(k) = yes$(ord(k) eq 1)        ;
last(k)  = yes$(ord(k) eq card(k))  ;

*==============================================================================
* Parameters Definition:
*==============================================================================

parameters

fh(i)      heat capacity flowrate of hot stream i
fc(j)      heat capacity flowrate of cold stream j
thin(i)    inlet temperature of hot stream i
thout(i)   outlet temperature of hot stream i
tcin(j)    inlet temperature of cold stream j
tcout(j)   outlet temperature of cold stream j
ech(i)     heat content of hot stream i
ecc(j)     heat content of cold stream j
hh(i)      stream-individual film coefficient hot i
hc(j)      stream-individual film coefficient cold j
hucost     cost of heating utility
cucost     cost of cooling utility
unitc      fixed charge for exchanger
acoeff     area cost coefficient for exchangers
hucoeff    area cost coefficient for heaters
cucoeff    area cost coefficient for coolers
aexp       cost exponent for exchangers
hhu        stream-individual film coefficient hot utility
hcu        stream-individual film coefficient cold utility
thuin      inlet temperature hot utility
thuout     outlet temperature hot utility
tcuin      inlet temperature cold utility
tcuout     outlet temperature cold utility
tmapp      minimum approach temperature
gamma(i,j) upper bound of driving force

HLmin
HLmax, HLmax1, HLmax2
;

*==============================================================================
* Variables Definition:
*==============================================================================

binary Variables

z(i,j,k)  existence of exchanger ijk
zcu(i,ColdU)    existence of cooler for hot stream i
zhu(j,HotU)    existence of heater for cold stream j;

positive Variables

th(i,k)    temperature of  hot stream i as it enters stage k
tc(j,k)    temperature of cold stream j as it leaves stage k
q(i,j,k)   energy exchanged between i and j in stage k
qc(i, ColdU)      energy exchanged between i and the cold utility
qh(j, HotU)      energy exchanged between j and the hot utility
dt(i,j,k)  approach between i and j at location k


dthuout(j,HotU)
dtcuout(i,ColdU)
dthuin(j,HotU)
dtcuin(i,ColdU)




;

variable
cost      Total Annual Cost (objective function);


*==============================================================================
* Equations:
*==============================================================================

equations

teh(i)        total energy exchanged by hot stream i
tec(j)        total energy exchanged by cold  stream j
eh(i,k)       energy exchanged by hot  stream i in stage k
ec(j,k)       energy exchanged by cold stream j in stage k
eqh(j,k)      energy exchanged by cold stream j with the hot utility
eqc(i,k)      energy exchanged by hot  stream i with the cold utility
month(i,k)    monotonicity of th
montc(j,k)    monotonicity of tc
monthl(i,k)   monotonicity of th k = last
montcf(j,k)   monotonicity of tc for k = 1
tinh(i,k)     supply temperature of hot streams
tinc(j,k)     supply temperature of cold streams
logqmax(i,j,k)   logical constraints on  q
logqmin(i,j,k)

logqh(j, HotU)      logical constraints on qh(j)
logqc(i, ColdU)      logical constraints on qc(i)
logdth(i,j,k) logical constraints on dt at the  hot end
logdtc(i,j,k)       "logical constraints on dt at the cold end"

logdthuout(j,k,HotU)
logdtcuout(i,k,ColdU)
logdthuin(j,HotU)
logdtcuin(i,ColdU)

obj                 "objective function"
ColdU_only(i)            "only one cold utility"
HotU_only(j)             "only one hot utility"

loghuin(j, k, HotU)      "to ensure the heat transfer in the inlet"
loghuout(j,HotU)         "to ensure the heat transfer in the outlet"

logcuin(i,k,ColdU)       "to cold utility ensure the heat transfer in the inlet"
logcuout(i,ColdU)        "to cold utility  ensure the heat transfer in the outlet"
;


teh(i).. (thin(i)-thout(i))*fh(i) =e= sum((j,st), q(i,j,st)) + sum(ColdU, qc(i, ColdU)) ;
tec(j).. (tcout(j)-tcin(j))*fc(j) =e= sum((i,st), q(i,j,st)) + sum(HotU, qh(j, HotU)) ;

eh(i,k)$st(k).. fh(i)*(th(i,k) - th(i,k+1)) =e= sum(j, q(i,j,k))  ;
ec(j,k)$st(k).. fc(j)*(tc(j,k) - tc(j,k+1)) =e= sum(i,q(i,j,k)) ;

eqc(i,k)$last(k)..  fh(i)*(th(i,k) - thout(i)) =e= sum(ColdU, qc(i, ColdU)) ;
eqh(j,k)$first(k).. fc(j)*(tcout(j) - tc(j,k)) =e= sum(HotU, qh(j, HotU)) ;

tinh(i,k)$first(k).. thin(i) =e= th(i,k) ;
tinc(j,k)$last(k)..  tcin(j) =e= tc(j,k) ;

month(i,k)$st(k).. th(i,k) =g= th(i,k+1) ;
montc(j,k)$st(k).. tc(j,k) =g= tc(j,k+1) ;

monthl(i,k)$last(k).. th(i,k) =g= thout(i) ;
montcf(j,k)$first(k)..tcout(j) =g= tc(j,k) ;

logqmax(i,j,k)$st(k)..q(i,j,k) - min(ech(i), ecc(j))*z(i,j,k) =l= 0 ;
logqmin(i,j,k)$st(k)..q(i,j,k) - HLmin*z(i,j,k) =g= 0;

logqc(i,ColdU)..
qc(i,ColdU) - ech(i)*zcu(i,ColdU) =l= 0 ;
logqh(j,HotU)..
qh(j,HotU) - ecc(j)*zhu(j,HotU) =l= 0 ;

logdth(i,j,k)$st(k)..dt(i,j,k) =l= th(i,k) - tc(j,k) +
                                   gamma(i,j)*(1 - z(i,j,k)) ;

logdtc(i,j,k)$st(k)..dt(i,j,k+1) =l= th(i,k+1)-tc(j,k+1) +
                                      gamma(i,j)*(1 - z(i,j,k)) ;

logdthuout(j,k,HotU)$first(k)..
dthuout(j,HotU)  =l= thuout(HotU) - tc(j,k) + 1.0e5*(1 - zhu(j,HotU));
logdtcuout(i,k,ColdU)$last(k)..
dtcuout(i,ColdU)  =l= th(i,k) - tcuout(ColdU) + 1.0e5*(1 - zcu(i,ColdU));


logdthuin(j,HotU)..
dthuin(j,HotU)  =l= thuin(HotU) - tcout(j) +1.0e5*(1 - zhu(j,HotU));
logdtcuin(i,ColdU)..
dtcuin(i,ColdU)  =l= thout(i) - tcuin(ColdU) +1.0e5*(1 - zcu(i,ColdU));



ColdU_only(i)..
sum(ColdU, zcu(i,ColdU)) =l= 1;
HotU_only(j)..
sum(HotU, zhu(j,HotU)) =l= 1;

loghuin(j, k, HotU)$first(k)..  thuout(HotU) - tc(j,k) =g= (zhu(j,HotU) - 1)*1.0e5;
loghuout(j,HotU)..   thuin(HotU) - tcout(j) =g= (zhu(j,HotU) - 1)*1.0e5;

logcuin(i,k,ColdU)$last(k)..  th(i,k) - tcuout(ColdU) =g= (zcu(i,ColdU) - 1)*1.0e5;
logcuout(i,ColdU)..   thout(i) - tcuin(ColdU) =g= (zcu(i,ColdU) - 1)*1.0e5;



obj..cost =e=
           unitc*(sum((i,j,st),z(i,j,st)) +
                  sum((i, ColdU),zcu(i,ColdU)) +
                  sum((j, HotU),zhu(j,HotU))) +
           sum((j, HotU), qh(j, HotU) * hucost(HotU)) +
           sum((i, ColdU),qc(i, ColdU)* cucost(ColdU))+

           acoeff*sum((i,j,k),(q(i,j,k)*((1/hh(i))+(1/hc(j)))/
               ((( dt(i,j,k)*dt(i,j,k+1)*(dt(i,j,k) + dt(i,j,k+1))/2 +
                  1e-9)**0.33333) + 1e-9) + 1e-6)**aexp) +
          sum(HotU,hucoeff(HotU)*(sum(j,(qh(j,HotU)*(  1/hc(j) +1/hhu(HotU)  ))/
               ((  dthuout(j,HotU)*dthuin(j, HotU)*((dthuout(j,HotU)+dthuin(j, HotU))/2)+
               1e-9)**0.33333) + 1e-9)**aexp))  +
          sum(ColdU,cucoeff(ColdU)*sum(i,(qc(i,ColdU)*((1/hh(i))+(1/hcu(ColdU)))/
               ((  dtcuin(i,ColdU)*dtcuout(i,ColdU)*(dtcuin(i,ColdU)+dtcuout(i,ColdU))/2 +
                  1e-9)**0.33333) + 1e-9)**aexp) );

equations obj2;
variable cost2;
obj2..cost2 =e= unitc*(sum((i,j,st),z(i,j,st)) +
                  sum((i, ColdU),zcu(i,ColdU)) +
                  sum((j, HotU),zhu(j,HotU))) +
                  sum((j, HotU),qh(j, HotU)*hucost(HotU)) +
                  sum((i,ColdU),qc(i,ColdU)*cucost(ColdU));

equations obj3;
variable cost3;
obj3..cost3 =e=   sum((j, HotU),qh(j, HotU)*hucost(HotU)) +
                  sum((i,ColdU),qc(i,ColdU)*cucost(ColdU));

*==============================================================================
* Model Definition:
*==============================================================================


Model specilized_model /
eh,ec, eqc,teh,eqh,tec,month,montc,monthl, montcf,tinh,tinc,
logqmax, logqmin
logqh,logqc,logdth, logdtc,

logdthuout, logdtcuout,logdthuin, logdtcuin
HotU_only, ColdU_only,

*loghuin, loghuout,logcuin, logcuout
obj
/ ;


Model specilized_model_mip /
eh,ec, eqc,teh,eqh,tec,month,montc,monthl,
montcf,tinh,tinc,
logqmax, logqmin

logqh,logqc,logdth, logdtc,

*logdtcu,logdthu,
HotU_only, ColdU_only,
loghuin, loghuout
logcuin, logcuout
obj2
/ ;

Model specilized_model3 /
eh,ec, eqc,teh,eqh,tec,month,montc,monthl, montcf,tinh,tinc,
logqmax, logqmin
logqh,logqc,logdth, logdtc,

logdthuout, logdtcuout,logdthuin, logdtcuin
HotU_only, ColdU_only,

*loghuin, loghuout,logcuin, logcuout
obj3
/ ;

*==============================================================================
* Process Parameters:
*==============================================================================

* process streams

* hot stream data:
table HSData(i,*)  "the parameters hot streams"
          tin             tout            HTC           FCp
H1        431.750         313.150         1.700         6.734
H2        452.850         313.150         1.700         7.114
H3        456.750         313.150         1.700         9.034
H4        509.250         313.150         1.700         634.880
H5        432.050         333.150         1.700         138.018




;
thin(i) = HSData(i,'tin');
thout(i) = HSData(i,'tout');
hh(i) = HSData(i,'HTC');
fh(i) = HSData(i,'FCp');


*cold
table CSData(j,*)  "the parameters cold streams"
          tin             tout            HTC           FCp
C1        487.950         493.150         1.700         578.526
C2        314.650         493.150         1.700         549.175
C3        313.150         520.550         1.700         68.226
C4        481.450         482.350         1.700         465.741
C5        384.950         386.650         1.700         670.261
;
tcin(j) = CSData(j,'tin');
tcout(j) = CSData(j,'tout');
hc(j) = CSData(j,'HTC');
fc(j) = CSData(j,'FCp');

* costs and coefficients
 unitc  =4000;   acoeff =146;  aexp   =0.6;


 tmapp = 20;


$ontext
 hucost =200;   hucoeff =146;  thuin  =240; thuout =240; hhu   =3.4;
 cucost =10;    cucoeff = 146; tcuin  =25;  tcuout =40; hcu   =1.7;

HotU  "Hot Uitlity"  /HU1*HU2/
ColdU "Cold Utility" /CU1*CU2/


$offtext


table CUData(ColdU,*)  "the parameters cold streams"
        tin           tout        HTC       cucoeff    cucost
CU1     397.15        398.15      60        146        -25.7
CU2     283.15        288.15      1.7       160        30
;
cucost(ColdU) =  CUData(ColdU,'cucost')  ;
cucoeff(ColdU) =  CUData(ColdU,'cucoeff')  ;
tcuin(ColdU) =  CUData(ColdU,'tin')  ;
tcuout(ColdU) =  CUData(ColdU,'tout')  ;
hcu(ColdU) =  CUData(ColdU,'HTC')  ;


table HUData(HotU,*)  "the parameters cold streams"
        tin           tout        HTC       hucoeff    hucost
HU1     543.15        542.15      6.0       150        34.1
HU2     448.15        447.15      6.0       150        30
;


hucost(HotU) =  HUData(HotU,'hucost')  ;
hucoeff(HotU) =  HUData(HotU,'hucoeff')  ;
thuin(HotU) =  HUData(HotU,'tin')  ;
thuout(HotU) =  HUData(HotU,'tout')  ;
hhu(HotU) =  HUData(HotU,'HTC')  ;
*==============================================================================
* Bounds:
*==============================================================================

dt.lo(i,j,k) = tmapp ;

dthuin.lo(j,HotU) = tmapp ;
dtcuin.lo(i,ColdU) = tmapp ;
dthuout.lo(j,HotU) = tmapp ;
dtcuout.lo(i,ColdU) = tmapp ;


th.up(i,k) = thin(i) ;
th.lo(i,k) = thout(i) ;
tc.up(j,k) = tcout(j) ;
tc.lo(j,k) = tcin(j) ;

*==============================================================================
* Initial Values:
*==============================================================================

th.l(i,k) = thin(i) ;
tc.l(j,k) = tcin(j) ;

dthuout.l(j,HotU) = thuout(HotU) - tcin(j) ;
dtcuout.l(i,ColdU) = thin(i) - tcuout(ColdU) ;

ech(i) = fh(i)*(thin(i) - thout(i)) ;
ecc(j) = fc(j)*(tcout(j) - tcin(j)) ;

HLmin = 40;
HLmax1 = smin(i,ech(i))  ;
HLmax2 = smin(j,ecc(j))  ;
HLmax = min(HLmax1,HLmax2);

gamma(i,j) = max(0,tcin(j) - thin(i), tcin(j) - thout(i),
                  tcout(j) - thin(i), tcout(j) - thout(i)) ;

dt.l(i,j,k) = thin(i) - tcin(j) ;

q.l(i,j,k)$st(k) = min(ech(i),ecc(j)) ;


*==============================================================================
* Solving the Problem:
*==============================================================================

option optcr    = 0 ;
option limrow   = 100;
option limcol   = 100;
option solprint = on;
option sysout   = on;
*option iterlim  = 100000 ;
option threads = 6;
option mip = gurobi;
option nlp = conopt;
option minlp = dicopt;
option reslim=3600;
option decimals = 6;


solve specilized_model3 using rminlp minimizing cost3;
abort$(specilized_model3.modelstat > 2.5) "Relaxed model could not be solved";

solve specilized_model3 using minlp minimizing cost3;

display q.l, z.l;
display zcu.l, zhu.l;

*$ontext
*===============================================================================
* NLP Improvment:
*===============================================================================

parameter
zs(i,j,k) existence of match beteen hot st. i and cold st. j at stage k
zcus(i, ColdU)   existence of cooler for hot stream i
zhus(j, HotU)   existence of heatr for cold strem j

;

* Given by the solution of MINLP model:

zs(i,j,k)=z.l(i,j,k);
zcus(i, ColdU)=zcu.l(i, ColdU);
zhus(j, HotU)=zhu.l(j, HotU);


Parameter
yh(i,k) pointer if hot stream i is split at stage k: (1) Yes (0) No

yc(j,k) pointer if cold stream j is split at stage k: (1) Yes (0) No;

* Pointers definition:

 yh(i,k)=0; yc(j,k)=0;

* when the stream is splitted:
 yh(i,k)$( sum(j,zs(i,j,k)) > 1)=1;
 yc(j,k)$( sum(i,zs(i,j,k)) > 1)=1;

*----------------------------------------------------------------------------
* Extra Variables needed for non-isothermal mixxing
*----------------------------------------------------------------------------

Positive Variables

   fhx(i,j,k) flowrate entering heat exchanegr ijk cold side
   fcx(i,j,k) flowrate entering heat exchanegr ijk hot side
   thx(i,j,k) outlet temperature of the heat exhanger ijk -hot side
   tcx(i,j,k) outlet temperature of the heat exhanger ijk -cold side;

*----------------------------------------------------------------------------
* Rewriten Equations with zs (parameters) instead z (variables)
*----------------------------------------------------------------------------

Equation
logqmaxs(i,j,k),
logqmins(i,j,k),
logqcs(i, ColdU),logqhs(j, HotU),
logqhmins(j, HotU), logqcmins(i, ColdU)
logdths(i,j,k),logdtcs(i,j,k)

;

logqmaxs(i,j,k)$st(k)..
q(i,j,k) - min(ech(i), ecc(j))*zs(i,j,k) =l= 0 ;
logqmins(i,j,k)$st(k)..
q(i,j,k) - HLmin*zs(i,j,k) =g= 0 ;

logqhmins(j, HotU)..
qh(j, HotU) - HLmin*zhus(j, HotU) =g= 0 ;
logqcmins(i, ColdU)..
qc(i,ColdU) - HLmin*zcus(i, ColdU) =g= 0 ;

logqcs(i, ColdU)..
qc(i,ColdU) - ech(i)*zcus(i, ColdU) =l= 0 ;
logqhs(j, HotU)..
qh(j, HotU) - ecc(j)*zhus(j, HotU) =l= 0 ;

logdths(i,j,k)$st(k)..dt(i,j,k) =l= th(i,k) - tcx(i,j,k) +
                                    gamma(i,j)*(1 - zs(i,j,k)) ;

logdtcs(i,j,k)$st(k)..dt(i,j,k+1) =l= thx(i,j,k)-tc(j,k+1) +
                                      gamma(i,j)*(1 - zs(i,j,k)) ;

*--------------------------------------------------------------------------
* Extra Equations due to non-isothermal mixxing:
*--------------------------------------------------------------------------

Equations

  mbh(i,k)      split mass balance for hot stream i at stage k
  mbc(j,k)      split mass balance for cold stream j at stage k
  ebhh(i,j,k)   heat exchanger energy balance aorund match ijk - hot side
  ebhc(i,j,k)   heat exchanger energy balance around match ijk-cold side
  ebmh(i,k)     mixer energy balance for hot stream i at stage k
  ebmc(j,k)     mixer energy balance for cold stream j at stage k;

* These Equations only hold if split ocuurs:

 mbh(i,k)$(st(k)$yh(i,k))..   fh(i)=e= sum(j, fhx(i,j,k) );
 mbc(j,k)$(st(k)$yc(j,k))..   fc(j)=e= sum(i, fcx(i,j,k) );

 ebhh(i,j,k)$(st(k)$yh(i,k))..   q(i,j,k)=e= fhx(i,j,k)*(th(i,k)   -thx(i,j,k));
 ebhc(i,j,k)$(st(k)$yc(j,k))..   q(i,j,k)=e= fcx(i,j,k)*(tcx(i,j,k) -tc(j,k+1));

 ebmh(i,k)$(st(k)$yh(i,k))..   fh(i)*th(i,k+1)=e=  sum(j, fhx(i,j,k)*thx(i,j,k));
 ebmc(j,k)$(st(k)$yc(j,k))..   fc(j)*tc(j,k)  =e=  sum(i, fcx(i,j,k)*tcx(i,j,k));

*--------------------------------------------------------------------------
* Extra Equations to define thx and tcx when no split occurs
* since the equations right above only hold if spli occurs, in case of non split
* it is necessary to define thx and tcx.
*--------------------------------------------------------------------------

Equations  e29a(i,j,k) defintion of thx for non-pslit case
           e29b(i,j,k) definition of tcx for non-split case;

 e29a(i,j,k)$(st(k)$ (yh(i,k) eq 0) ).. thx(i,j,k)=e=th(i,k+1);
 e29b(i,j,k)$(st(k)$ (yc(j,k) eq 0) ).. tcx(i,j,k)=e=tc(j,k);

equations
logdthuouts(j,k,HotU)
logdtcuouts(i,k,ColdU)
logdthuins(j,HotU)
logdtcuins(i,ColdU)
;



logdthuouts(j,k,HotU)$first(k)..
dthuout(j,HotU)  =l= thuout(HotU) - tc(j,k)
                  +1.0e5*(1 - zhus(j,HotU))
;
logdtcuouts(i,k,ColdU)$last(k)..
dtcuout(i,ColdU)  =l= th(i,k) - tcuout(ColdU)
                  +1.0e5*(1 - zcus(i,ColdU))
;


logdthuins(j,HotU)..
dthuin(j,HotU)  =l= thuin(HotU) - tcout(j)
                  +1.0e5*(1 - zhus(j,HotU))
;
logdtcuins(i,ColdU)..
dtcuin(i,ColdU)  =l= thout(i) - tcuin(ColdU)
                  +1.0e5*(1 - zcus(i,ColdU))
;









*--------------------------------------------------------------------------
* Objetive Function
*--------------------------------------------------------------------------

equation obj4;

variable cost4;

obj4..cost4 =e= unitc*(sum((i,j,st),zs(i,j,st)) +
                        sum((i, ColdU),zcus(i,ColdU)) +
                        sum((j, HotU),zhus(j,HotU))) +
                sum((j, HotU), qh(j, HotU) * hucost(HotU)) +
                sum((i, ColdU),qc(i, ColdU)* cucost(ColdU)) +

                acoeff*sum((i,j,k),(q(i,j,k)*((1/hh(i))+(1/hc(j)))/
                           (((dt(i,j,k)*dt(i,j,k+1)*(dt(i,j,k) + dt(i,j,k+1))/2 +
                              1e-9)**0.33333) + 1e-9) + 1e-9)**aexp) +
          sum(HotU,hucoeff(HotU)*(sum(j,(qh(j,HotU)*(  1/hc(j) +1/hhu(HotU)  ))/
               ((  dthuout(j,HotU)*dthuin(j, HotU)*((dthuout(j,HotU)+dthuin(j, HotU))/2)+
               1e-9)**0.33333) + 1e-9)**aexp))  +
          sum(ColdU,cucoeff(ColdU)*sum(i,(qc(i,ColdU)*((1/hh(i))+(1/hcu(ColdU)))/
               ((  dtcuin(i,ColdU)*dtcuout(i,ColdU)*(dtcuin(i,ColdU)+dtcuout(i,ColdU))/2 +
                  1e-9)**0.33333) + 1e-9)**aexp) );


equation obj5;

variable cost5;

obj5..cost5 =e=
                sum((j, HotU), qh(j, HotU) * hucost(HotU)) +
                sum((i, ColdU),qc(i, ColdU)* cucost(ColdU)) ;





Model superbasic_nlp /
mbh,mbc,

ebhh,ebhc,

ebmh,ebmc,
eh,ec,eqc,  teh,eqh,tec,month,montc,monthl
,e29a,e29b,
 montcf,tinh,tinc,

logqmaxs,logqmins,

logqhs,logqcs,logdths, logdtcs,

logdthuouts,logdtcuouts,logdthuins,logdtcuins

obj4
/ ;

Model superbasic_nlp_Utility /
mbh,mbc,

ebhh,ebhc,

ebmh,ebmc,
eh,ec,eqc,  teh,eqh,tec,month,montc,monthl
,e29a,e29b,
 montcf,tinh,tinc,

logqmaxs,logqmins,

logqhs,logqcs,logdths, logdtcs, logqhmins,  logqcmins,

logdthuouts,logdtcuouts,logdthuins,logdtcuins

obj5
/ ;



*----------------------------------------------------------------------------
* Bounds for the new variables
*----------------------------------------------------------------------------
*Bounds:
fhx.up(i,j,k)=fh(i);
fcx.up(i,j,k)=fc(j);
thx.lo(i,j,k)=thout(i);
thx.up(i,j,k)=thin(i);
tcx.lo(i,j,k)=tcin(j);
tcx.up(i,j,k)=tcout(j);

*----------------------------------------------------------------------------
* Initial Values:  Giveing the Isothermal Mixing Assumtpion
*----------------------------------------------------------------------------

thx.l(i,j,k)$st(k)=th.l(i,k+1);
tcx.l(i,j,k)$st(k)=tc.l(j,k);

parameter denh(i,k),denc(j,k);
denh(i,k) = sum(j, q.l(i,j,k));
denc(j,k) = sum(i, q.l(i,j,k));

fhx.l(i,j,k)=fh(i)*q.l(i,j,k)/(denh(i,k)+1e-6);
fcx.l(i,j,k)=fc(j)*q.l(i,j,k)/(denc(j,k)+1e-6);

fhx.fx(i,j,k)$(q.l(i,j,k) eq 0)=0;
fcx.fx(i,j,k)$(q.l(i,j,k) eq 0)=0;


option nlp= conopt;
superbasic_nlp_Utility.holdfixed=1;


parameter flag;
flag= sum((i,k), yh(i,k))+sum((j,k), yc(j,k));
if( flag eq 0,

display "--------------------- NO STREAM SPLIT ----------------------------";
else

option nlp = conopt;
solve superbasic_nlp_Utility using nlp minimizing cost5 ;
display "-----------------ISOTHERMAL MIXING ASSUMPTION REMOVED -----------";
);

*$offtext

display z.l, q.l, zcu.l, qc.l, zhu.l, qh.l;


parameter
lmtdp(i,j,k) log mean temperature difference for exchanger ijk
lmtdcup(i, ColdU)   log mean temperature difference cooler i
lmtdhup(j, HotU)   log mean temperature difference heater j
a(i,j,k)     area for exchanger for match ij in interval k (chen approx.)
al(i,j,k)    area for exchanger for match ij in interval k calculated with log mean
acul(i, ColdU)       area cooler i
ahul(j, HotU)       area heater j
costheat     Cost of heating
costcool     Cost of cooling
opercost     Operating Cost
nz           Number of units
invcost      Investment Cost
TAC          Total Annual Cost;

* Log Mean Temperature difference:

lmtdp(i,j,k)$(st(k)$ (q.l(i,j,k) gt 0.1*HLmin))=(dt.l(i,j,k)-dt.l(i,j,k+1))/log(dt.l(i,j,k)/dt.l(i,j,k+1)+1.0e-9);
lmtdcup(i, ColdU)$((zcu.l(i, ColdU) eq 1) and (dtcuin.l(i,ColdU)/ dtcuout.l(i,ColdU) ne 1) ) =(dtcuin.l(i,ColdU)-dtcuout.l(i,ColdU))/log(dtcuin.l(i,ColdU)/ dtcuout.l(i,ColdU));
lmtdcup(i, ColdU)$((zcu.l(i, ColdU) eq 1) and (dtcuin.l(i,ColdU)/ dtcuout.l(i,ColdU) eq 1) ) =(dtcuin.l(i,ColdU)+dtcuout.l(i,ColdU))/2;


lmtdhup(j, HotU)$((zhu.l(j, HotU) eq 1) and (dthuout.l(j, HotU)/ dthuin.l(j,HotU) ne 1 ))=( dthuout.l(j,HotU)-dthuin.l(j, HotU))/log( dthuout.l(j, HotU)/ dthuin.l(j,HotU) );
lmtdhup(j, HotU)$((zhu.l(j, HotU) eq 1) and (dthuout.l(j, HotU)/ dthuin.l(j,HotU) eq 1 ))=( dthuout.l(j,HotU)+dthuin.l(j, HotU))/2;

*  Areas estimated by chen approximation

a(i,j,k)$(st(k)$ (z.l(i,j,k) eq 1)) = q.l(i,j,k)*((1/hh(i))+(1/hc(j)))/
                  (2/3*sqrt(dt.l(i,j,k)*dt.l(i,j,k+1)) +
                   1/6*( dt.l(i,j,k) + dt.l(i,j,k+1))) ;
a(i,j,k)$(st(k)$ (z.l(i,j,k) eq 0)) = 0;

*  Areas by log mean temperature
$ontext
al(i,j,k)$(st(k)$ (z.l(i,j,k) eq 1))  = q.l(i,j,k)*((1/hh(i))+(1/hc(j)))/lmtdp(i,j,k);
al(i,j,k)$(st(k)$ (z.l(i,j,k) eq 0))  = 0;
$offtext
* Areas of heaters and Coolers

ahul(j,HotU)$(zhu.l(j, HotU) eq 1) = qh.l(j,HotU)*((1/hc(j)) + (1/hhu(HotU)))/(lmtdhup(j, HotU));
acul(i,ColdU)$(zcu.l(i, ColdU) eq 1) = qc.l(i,ColdU)*((1/hh(i))+(1/hcu(ColdU)))/(lmtdcup(i, ColdU));


*  Operating Costs:

costheat = sum((j, HotU), qh.l(j, HotU) * hucost(HotU)) ;
costcool = sum((i, ColdU),qc.l(i, ColdU)* cucost(ColdU)) ;
opercost = costheat+costcool ;




* Investment cost

nz=( sum((i,j,k), z.l(i,j,k))+ sum((i, ColdU),zcus(i,ColdU))+sum((j, HotU),zhus(j,HotU)));
invcost = unitc*(nz)+
          acoeff*( sum((i,j,k), a(i,j,k)**aexp)+
          sum((i,ColdU),acul(i,ColdU)**aexp)+sum((j,HotU),ahul(j,HotU)**aexp));


* Total Annual Cost

 TAC= invcost+opercost;

parameters
over1(i,j,k)
over2(i,j,k)
;

over1(i,j,k) $(st(k)$ (q.l(i,j,k) gt 0.1*HLmin)) = log(dt.l(i,j,k)/dt.l(i,j,k+1));
over2(i,j,k) $(st(k)$ (q.l(i,j,k) gt 0.1*HLmin)) = dt.l(i,j,k)-dt.l(i,j,k+1);

display  z.l;
display z.l, zcu.l, zhu.l;
display q.l, qh.l, qc.l;
display a,  acul, ahul;
*display al;
*display  dt.l;
*display over1, over2;
