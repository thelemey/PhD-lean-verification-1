#!/usr/bin/env python3
"""Finite independent checks of normalization and corrected boundary cases.
These checks corroborate the written proofs; they are not replacements for them.
"""
from decimal import Decimal, localcontext
from fractions import Fraction
from math import comb
from pathlib import Path
import json

checks=0
def check(condition,detail):
    global checks
    assert condition,detail
    checks+=1

# Independent coefficient extraction for a rational formal generating function.
def rational_coefficients(k,p,t,count):
    r=k+p-1
    den=[0]*(r+1);den[0]=1;den[1]=-t
    for j in range(p+1,r+1):den[j]-=1
    out=[]
    for n in range(count):
        val=int(n==r-1)
        for j in range(1,min(n,r)+1):val-=den[j]*out[n-j]
        out.append(val)
    return out

def recurrence(k,p,t,count):
    r=k+p-1;a=[0]*(r-1)+[1]
    while len(a)<count:
        n=len(a)
        a.append(t*a[n-1]+sum(a[n-j] for j in range(p+1,r+1)))
    return a[:count]

for k in range(2,8):
    for p in range(1,6):
        for t in (1,2,5):
            a=recurrence(k,p,t,45)
            b=rational_coefficients(k,p,t,45)
            check(a==b,("rational coefficients",k,p,t))
            check(a[k+p-2]==1,("initial unit",k,p,t))
check(recurrence(2,1,1,11)==[0,1,1,2,3,5,8,13,21,34,55],"ordinary Fibonacci")
check(recurrence(3,1,1,10)==[0,0,1,1,2,4,7,13,24,44],"order-three specialization")
check(recurrence(2,2,1,9)==[0,0,1,1,1,2,3,4,6],"lag-three specialization")

fib=recurrence(2,1,1,50)
for n in range(40):
    check(sum(comb(n-k,k) for k in range(n//2+1))==fib[n+1],
          ("corrected binomial index",n))

# Maximal finite factors of period q_n in independently generated mechanical words.
# A run of R equalities w[i]=w[i+q] gives a factor of length R+q with period q.
def maximal_periodic_length(word,q):
    best=run=0
    for i in range(len(word)-q):
        if word[i]==word[i+q]:
            run+=1;best=max(best,run)
        else:run=0
    return q+best

sturmian_cases=[]
with localcontext() as ctx:
    ctx.prec=60
    phi=(Decimal(1)+Decimal(5).sqrt())/2
    for prefix in ([2],[3,2],[2,3,1],[4,1,2]):
        tail=phi
        for a in reversed(prefix):tail=Decimal(a)+1/tail
        beta=1/tail
        word=[int(((i+2)*beta)//1-((i+1)*beta)//1) for i in range(60000)]
        digits=list(prefix)+[1]*10
        q_prev,q_cur=0,1
        qs=[1]
        for a in digits:
            q_prev,q_cur=q_cur,a*q_cur+q_prev
            qs.append(q_cur)
        for n in range(1,7):
            q=qs[n]
            expected=2*q+qs[n+1]-2
            actual=maximal_periodic_length(word,q)
            check(actual==expected,("Sturmian periodic factor",prefix,n,q,actual,expected))
            sturmian_cases.append({"cf_prefix":prefix,"n":n,"period":q,
                                   "max_length":actual,"exponent":str(Fraction(actual,q))})

y0,y1="01","02"
check(not y1.startswith(y0),"the original n=0 counterexample")
check(len({y0[i:j] for i in range(2) for j in range(i+1,3)
           if y0[i:j]==y0[i:j][::-1]})==2,"separate richness of y0")
for n in range(1,12):
    y2=y1+y0
    check(y2.startswith(y1),("corrected nesting",n))
    y0,y1=y1,y2

for b in range(2,25):
    for j in range(b,35):
        check(2*b//j<=2,("corrected final branch",b,j))
check(2*7//7==2,"the sharp j'=b boundary")

source=(Path(__file__).parent/"thesis_corrected.tex").read_text()
for obsolete in (
    "она обладает более слабым, но существенным свойством распределения",
    "F_{k-p-1}^p(t,k) = 1",
    r"= 2 \limsup_{n \to \infty}",
    r"\lfloor 2b/j'\rfloor\le1",
):
    check(obsolete not in source,("obsolete critical text",obsolete))
for required in ("eq:correct-index","eq:correct-asymptotic-index",
                 r"\sum_{j=p+1}^{r}",r"\frac1H+\frac{2}{|\tau|H}"):
    check(required in source,("required proof text",required))

report={"checks_passed":checks,"sturmian_period_cases":sturmian_cases,
        "scope":"Finite corroboration and text-consistency checks; mathematical proofs are in the TeX documents."}
(Path(__file__).parent/"verification_results.json").write_text(
    json.dumps(report,ensure_ascii=False,indent=2),encoding="utf-8")
print(json.dumps({"checks_passed":checks,"sturmian_period_cases":len(sturmian_cases)}))
