#!/bin/python

    #Our sets, X, Y, and Homomorphism##This lists should 
    #be edited if we want to use different elements
    #Note that 'Z' denotes Zero (0), and 'O' denotes One (1)
X=['O','a','b','c','d']
Y=['k','f','g','h','j']
Homo=X

    #importing the data
import random
import pandas as pd
import numpy as np
from itertools import product
import time
import subprocess
#
r1= pd.read_csv("X.csv", header=None)
t1= pd.read_csv("Y.csv", header=None)
h1= pd.read_csv("Homo.csv", header=None)

r2=pd.DataFrame(r1)
t2=pd.DataFrame(t1)
h2=pd.DataFrame(h1)


class fill:
    ##Filling Section:
    #\\fill the homomorphism table
    def homomorphism(val):
        if val not in X and val!=0 and val!='X' and val!='k':
            ind = np.random.randint(0,len(Y)-1)
            val = Y[ind]
        return val
    #\\fill Y table
    def Y(val):
        if val not in Y and val!='*':
            ind = np.random.randint(0,len(Y)-1)
            val = Y[ind]
        return val
    #convert 'nan' values from the excel sheet into np.nan:
    def nan(val):
        if val=='nan':
            val=np.nan
        return val

    #applying nan() to the DataFrames
r=r2.applymap(fill.nan)
t=t2.applymap(fill.nan)
h=h2.applymap(fill.nan)


    #remove repeated elements
def uni(T):
    dr=[]
    df=[]
    do=[]
    for x in T:
        dr.append(set(x))
    for x in dr:
        if x not in df:
            df.append(x)
    for x in df:
        do.append(list(x))
    return do

def univ(T):
    df=[]
    for x in T:
        if x not in df:
            df.append(x)
    return df

    #run beep after complete task
def pl():
	subprocess.Popen(['mpg123', '-q', 'beep-07.mp3'])


    #Multiplication Function
def M(R,C):
    if R and C in X:
        i=X.index(R)+1
        j=X.index(C)+1
        OUT=r[j][i]             #r[col][row]
    if R and C in Y:
        i=Y.index(R)+1
        j=Y.index(C)+1
        OUT=t[j][i]
    return OUT
    #\\Homomorphism Function
def H(R):   
    i=X.index(R)+1
    j=X.index(R)+1
    OUT=h[j][i]             #h[col][row]
    return OUT


    ##AXIOMS:
    #\\X GE, comm, trans axioms
class gex:
    #check GE-algebra axioms
    def ge(T):
        T=list(T)
        if T[0] in X :
            dt='O'
        elif T[0] in Y:
            dt='k'
        C1=True
        C2=True
        C3=True
        if dt not in T:
            K='not GE, since it doesnt have the 1 element'
            return K
        for x, y, z in product(T,T,T):
            if M(x,M(y,z))!=M(x,M(y,M(x,z))):
                C3=False
                break
            if M(dt,x)!=x:
                C1=False
                break
            if M(x,x)!=dt:
                C2=False
                break
        C0=C1==C2==C3
        return C0

    #check commutative property
    def comm(T):
        T=list(T)
        B=True
        for x,y in product(T,T):
            if M(M(y,x),x)!=M(M(x,y),y):
                B=False
                break
        return B

    #check transitive property
    def trans(T):
        T=list(T)
        if T[0] in X :
            dt='O'
        elif T[0] in Y:
            dt='k'
        Q=True
        for x,y,z in product(T,T,T):
            if M(M(x,y),M(M(z,x),M(z,y)))!=dt:
                Q=False
                break
        return Q

    #find subalgebras of R
    def sub(R):
        R=list(R)
        tic = time.perf_counter()
        if R==X:
            dt='O'
        elif R==Y:
            dt='k'
        if gex.ge(R)==True:
            D=[]
            D.append({dt})
            for a,b,c,d,e,f in product(R,R,R,R,R,R):
                if {dt,a,b,c,d,e,f} not in D:
                    if gex.ge([dt,a,b,c,d,e,f])==True:
                        S={dt,a,b,c,d,e,f}
                        D.append(S)
            toc = time.perf_counter()
            print(f"{toc - tic:0.4f} seconds")
            pl()
            return univ(D)
        else:
            print(R,' isnt a GE')


    #\\check ge,trans,comm,hilbert by one shot
    def chge(R):
        R=list(R)
        print(R,' is GE: ',gex.ge(R),', is transitive: ',gex.trans(R),', is commutative:',gex.comm(R),', is Hilbert algebra:',hilbert.h0(R))


    #check the subalgebras product if satisfies GE-algebra axioms
    def f(R):
        R=list(R)
        tic = time.perf_counter()
        SUBALGEBRAS=gex.sub(R)
        C=0
        D=0
        for x,y in product(SUBALGEBRAS,SUBALGEBRAS):
            TP=[]
            Tp=[]
            for x1,y1 in product(x,y):
                TP.append(M(x1,y1))
                Tp.append(M(y1,x1))
            Tp=list(set(Tp))
            TP=list(set(TP))
            if gex.ge(Tp) is True:
                print(Tp,' is ',y,' * ',x)

            if gex.ge(TP) is True:
                print(TP,' is ',x,' * ',y)
        toc = time.perf_counter()
        print(f"{toc - tic:0.4f} seconds")
        pl()

        #\\Hilbert algebra:
class hilbert:
    #Check hilbert algebra axioms
    def h0(T):
        T=list(T)
        if T[0] in X :
            dt='O'
        elif T[0] in Y:
            dt='k'
        h1=True
        h2=True
        h3=True
        for x,y,z in product(T,T,T):
            if M(M(x,M(y,z)),M(M(x,y),M(x,z)))!=dt:
                h2=False
                break
            if M(x,M(y,x))!=dt:
                h1=False
                break
            if M(x,y)==M(y,x)==dt and x!=y:
                h3=False
                break
        h0=h1==h2==h3
        return h0
    #find hilbert subalgebras
    def sub(R):
        R=list(R)
        tic = time.perf_counter()
        if R==X:
            dt='O'
        elif R==Y:
            dt='k'
        if hilbert.h0(R)==True:
            D=[]
            D.append({dt})
            for a,b,c,d,e,f in product(R,R,R,R,R,R):
                if {dt,a,b,c,d,e,f} not in D:
                    if hilbert.h0([dt,a,b,c,d,e,f])==True:
                        S={dt,a,b,c,d,e,f}
                        D.append(S)
            pl()
            toc = time.perf_counter()
            print(f"{toc - tic:0.4f} seconds")
            return univ(D)
        else:
            print(R,' is not hilbert')


    ##Filters:
class filtr:
    #filter axioms
    def f0(D,R):
        D=list(D)
        R=list(R)
        if D[0] in X:
            dt='O'
        elif D[0] in Y:
            dt='k'
        F1=True
        F2=True
        for x,y in product(D,R):
            if dt not in D:
                F1=False
                break
            if M(x,y) in D:
                if y not in D:
                    F2=False
                    break
        F0=F1==F2
        return F0
    #find filters of GE-algebra
    def find(R):
        R=list(R)
        tic = time.perf_counter()
        if R==X:
            dt='O'
        if R==Y:
            dt='k'
        if gex.ge(R)==True:
            D=[]
            D.append({dt})
            for a,b,c,d,e,f in product(R,R,R,R,R,R):
                if {dt,a,b,c,d,e,f} not in D:
                    if filtr.f0([dt,a,b,c,d,e,f],R)==True:
                        S={dt,a,b,c,d,e,f}
                        D.append(S)
            toc = time.perf_counter()
            print(f"{toc - tic:0.4f} seconds")
            pl()
            return univ(D)
        else:
            print(R,' is not GE-algebra')
    #find composition series
    def comb_series(GE):
        
        tic = time.perf_counter()
        Q=filtr.find(GE)
        for y in Q:
            check =  all(item in y for item in ['O'])
            if check is True:
                print(y)
        toc = time.perf_counter()
        print(f"{toc - tic:0.4f} seconds")
        pl()
    #find filter series
    def filt_series(GE,Filter):
        tic = time.perf_counter()
        for y in filtr.find(GE):
            check =  all(item in y for item in Filter)
            if check is True:
                print(y)
        toc = time.perf_counter()
        print(f"{toc - tic:0.4f} seconds")
        pl()

		
    #congruence relation:
class cgr:
    #if a and b are congruence in K
    def cong(a,b,K):
        cong=True
        if M(a,b) not in K or M(b,a) not in K:
            cong=False
        return cong


    #\\find the congruent elements in R of a subalgebra C

    def fcg(R,C):
        cd=[]
        cf=[]
        for x,y in product(C,C):
            if cgr.cong(x,y,R)==True:
                cf.append([x,y])
        pl()
        return uni(cf)
        
    #\\find the congruent kernel in R

    def krnlcgr(R,C):
        if R[0] in X:
            dt='O'
        elif R[0] in Y:
            dt='k'
        kf=[]
        kd=[]
        for x in C:
            if cgr.cong(dt,x,R)==True:
                kf.append(x)
        for b in kf:
            if b not in kd:
                kd.append(b)
        if set(kd)==set(R):
            print('closed filter')
        return kd

    #the congruence class of v in Filter of GE
    def cgrx(v,Filter,GE):
        kf=[]
        kd=[]
        for x in GE:
            if cgr.cong(v,x,Filter)==True:
                kf.append(x)
        for b in kf:
            if b not in kd:
                kd.append(b)
        return kd
    #find the quotient GE over Filter
    def over(GE,Filter):
        of=[]
        od=[]
        for x in GE:
            of.append(cgr.cgrx(x,Filter,GE))
        pl()
        return uni(of)
    #find the quotient GE over Filter and print them element by element
    def overr(GE,Filter):
        for x in GE:
            print(x,cgr.cgrx(x,Filter,GE))
        pl()


    #homomorphism
class homo:
    #\\Find the image of a subset of GE-algebra, say R
    def himage(R):
        image=[]
        J=[]
        for x in R:
            J.append(H(x))
        for x in J:
            if x not in image:
                image.append(x)
        return image

        ##Check Section:
        #\\Check X is homomorphism into Y, by replace X instead of R
    def homo(R):
        HHH=True
        for x,y in product(R,R):
            if H(M(x,y))!=M(H(x),H(y)):
                HHH=False
                break
        return HHH


        #\\find Y table satisfies the homomorphism table

    def fY():
        global t
        t0=t
        while True:
            t=t0
            t=t.applymap(fill.Y)
            if gex.ge(Y)==True:
                if homo.homo(X)==True:
                    print(t)
                    pl()
                    break

    #construct a non-transitive GE-algebra with non-transitive congruence relation
    def ffY():
        global t
        t0=t
        while True:
            t=t0
            t=t.applymap(fill.Y)
            if gex.ge(Y)==True:
                if gex.trans(Y)==False:
                    phi=filtr.find(Y)
                    n=np.random.randint(0,len(phi)-1)
                    if phi[n]!=['k'] and np.any({'k','g','f','h'}) not in phi[n]:
                        Phi=phi[n]
                    else:
                        continue
                    for x,y,z in product(Y,Y,Y):
                        if cgr.cong(x,y,Phi)==cgr.cong(y,z,Phi)==True:
                            if cgr.cong(x,z,Phi)==False:
                                print(t)
                                pl()
                                break



        #\\find homomorphism table that is epimorphism

    def fepi():
        tic = time.perf_counter()
        global h
        h0=h
        hd=[]
        while True:
            hp=[]
            h=h0
            h=h.applymap(fill.homomorphism)
            for i in [1,2,3,4,5]:
                hp.append(h[i][i])
            if set(hp)==set(Y):
                if hp not in hd:
                    hd.append(hp)
                    if homo.homo(X)==True:
                        print(h)
                        toc = time.perf_counter()
                        print(f"{toc - tic:0.4f} seconds")
                        pl()
                        break
  

    def fepi2():
        tic = time.perf_counter()
        global h
        h0=h
        hd=[]
        while True:
            hp=[]
            h=h0
            h=h.applymap(fill.homomorphism)
            for i in [1,2,3,4,5]:
                hp.append(h[i][i])
            if hp not in hd:
                hd.append(hp)
                if homo.homo(X)==True:
                    print(h)
                    toc = time.perf_counter()
                    print(f"{toc - tic:0.4f} seconds")
                    break
