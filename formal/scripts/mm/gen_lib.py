import os,sys,itertools
MACH=os.environ.get('MACH','PP'); IDN=os.environ.get('IDN','zpp')
os.environ['LOGIC']='Logic'+MACH; os.environ['LOGICID']=IDN
HERE=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,os.path.join(HERE,'..')); ROOT=os.path.join(HERE,'..','..')
import symexec as S
KIND={'bits':[2,3],'Z2':[2],'T3':[3],'NB':[1,2,3],'ALL':[0,1,2,3],'O13':[1,3]}
def s(a): return ('s',a)
def p(n): return ('p',n)
def b(i,f='id'): return ('b',i,f)
def expr(items,names):
    acc='[]'
    for it in reversed(items):
        if it[0] in 's p'.split():
            v=str(it[1])
            acc='[%s]'%v if acc=='[]' else '%s :: (%s)'%(v,acc)
        else:
            x=names[it[1]]
            if it[2]!='id': x='List.replicate %s.length %d'%(x,it[2])
            acc=x if acc=='[]' else '%s ++ (%s)'%(x,acc)
    return acc
def lit(items,sub=None):
    o=[]
    for it in items:
        if it[0]=='s': o.append('.sym %d'%it[1])
        elif it[0]=='p': o.append('.sym %d'%sub[it[1]])
        else: o.append('.blk %d %s'%(it[1],'.id' if it[2]=='id' else '(.const %d)'%it[2]))
    return '['+', '.join(o)+']'
def conc(items,sub):
    return [('s',sub[it[1]]) if it[0]=='p' else it for it in items]
HYP={'bits':'(h{n} : Bits {n})','Z2':'(h{n} : ∀ a ∈ {n}, a ∈ Z2)','T3':'(h{n} : ∀ a ∈ {n}, a ∈ T3)','NB':'(h{n} : NoB {n})','ALL':'(h{n} : Sym4 {n})','O13':'(h{n} : ∀ a ∈ {n}, a ∈ O13)'}
SETN={'bits':'bits','Z2':'Z2','T3':'T3','NB':'NB','ALL':'ALL','O13':'O13'}
import re as _re
_QF=set(_re.findall(r'def (\w+) : Nat', open(os.path.join(ROOT,'ZP','LogicF.lean')).read()))
def qn(q):
    if S.Q[q]<129: return 'Q.'+q
    if MACH in ('D','G') and q in _QF: return 'QF.'+q
    return 'Q%s.%s'%(MACH,q)

def theorem(name,doc,vars_,params,start,end,tt='FF'):
    """vars_: [(name,kind)]; params: [name] symbols in bits; start/end: (state, left items, right items)"""
    names=[v for v,_ in vars_]
    kinds=[k for _,k in vars_]
    sets=[KIND[k] for k in kinds]
    binders=' '.join('(%s : List Nat)'%v for v in names)+''.join(' (%s : Nat)'%q for q in params)
    hyps=' '.join(HYP[k].format(n=n) for n,k in vars_)+''.join(' (h%s : %s ∈ bits)'%(q,q) for q in params)
    def stm(t,dl):
        q,l,r=t
        return '%s %s (%s) (%s)'%('hd' if dl else 'hdR',qn(q),expr(l,names),expr(r,names))
    sdl= tt[0]=='T'; edl= tt[1]=='T'
    head='/-- %s -/\ntheorem %s %s %s :\n    %sLogic.Reach (%s)\n      (%s) := by\n'%(doc,name,binders,hyps,IDN,stm(start,sdl),stm(end,edl))
    valid='Valid [%s] [%s] := %s'%(', '.join(SETN[k] for k in kinds),', '.join(names),
        ''.join('Valid.cons h%s ('%n for n in names)+'Valid.nil _'+')'*len(names))
    head+='  have hV : %s\n'%valid
    body=''
    envs='[%s]'%', '.join(names)
    cases=list(itertools.product(*[[2,3]]*len(params)))
    def one(sub,indent):
        k=S.reachN(sets,[],S.sc(start[0],conc(start[1],sub),conc(start[2],sub),sdl),S.sc(end[0],conc(end[1],sub),conc(end[2],sub),edl))
        if k is None:
            c0=S.sc(start[0],conc(start[1],sub),conc(start[2],sub),sdl)
            print('NO PATH',name,sub,S.show(S.run(sets,c0,limit=100000)[1]),file=sys.stderr); k=-1
        return ('%sexact check%s (env := %s) (E := []) (k := %d) hV trivial\n%s  (ls := %s) (rs := %s)\n%s  (ls\' := %s) (rs\' := %s)\n%s  (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)\n'
            %(indent,tt,envs,k,indent,lit(start[1],sub),lit(start[2],sub),indent,lit(end[1],sub),lit(end[2],sub),indent))
    if not params:
        body=one({}, '  ')
    else:
        pat=' | '.join(['rfl']*len(params)) 
        # nested rcases
        body=''
        for q in params:
            body+='  rcases mem_bits h%s with rfl | rfl\n'%q if False else ''
        # use a single rcases pattern per param, then bullets
        rc=' <;> '.join('rcases mem_bits h%s with rfl | rfl'%q for q in params)
        body='  %s\n'%rc
        for sub in itertools.product(*[[2,3]]*len(params)):
            sd=dict(zip(params,sub))
            body+='  · '+one(sd,'    ').lstrip()
    return head+body+'\n'
