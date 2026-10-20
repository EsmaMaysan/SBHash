import argparse
import csv
import math
from pathlib import Path

P = 5
ELL = 64
R = 528
M = 192


def d_local(t):
    return 1 + t * (P - 1) + math.comb(t, 2) * (P - 1) ** 2


def balanced_local_log_count(nblocks):
    f, b = divmod(R, nblocks)
    if f > ELL or (b and f + 1 > ELL):
        return None
    return (nblocks - b) * math.log2(d_local(f)) + b * math.log2(d_local(f + 1))


def regular_collision_exponent():
    values = []
    for m0 in range(math.ceil(R / ELL), M + 1):
        z = balanced_local_log_count(m0)
        if z is not None:
            values.append((R * math.log2(P) - z + math.log2(P - 1), m0))
    return min(values)


def anchored_linearization_exponent():
    values = []
    for h in range(math.ceil(R / ELL), M):
        z = balanced_local_log_count(h)
        if z is not None:
            values.append((R * math.log2(P) - z, h))
    return min(values)


def run(quick=False):
    from p_ary_linearization_wagner_optimizer import pure_wagner_results
    from p_ary_regular_prange_optimizer import regular_prange_result
    from official_large_field_rsd_benchmark import agb2_large_field_benchmark, hybrid_large_field_benchmark
    results = {}
    z,m0=regular_collision_exponent()
    results['Regular collision decoding']=(z,'m0='+str(m0))
    z,h=anchored_linearization_exponent()
    results['Linearization with nonzero anchor']=(z,'h='+str(h))
    w=pure_wagner_results(P,ELL,R,M)
    best=min(w,key=lambda x:x.time_exponent)
    results['Pure Wagner']=(best.time_exponent,'nu='+str(best.nu))
    pr=regular_prange_result(P,ELL,R,M)
    results['Regular-Prange']=(pr.success_exponent,'f='+str(pr.f)+', b='+str(pr.b))
    n=M*ELL
    agb=agb2_large_field_benchmark(n,n-R,M)
    if agb:
        best=agb[0]
        results['AGB 2.0']=(best.cost,'f='+str(best.f)+', mu='+str(best.mu))
    hy=hybrid_large_field_benchmark(n,n-R,M)
    results['Hybrid RSD']=(hy.cost,'u='+str(hy.u)+', q='+str(hy.q)+', f='+str(hy.f))
    if not quick:
        from p_ary_regular_isd_optimizer_unrestricted import optimize_p_ary_regular_isd
        from p_ary_regular_isd_preimage_enum import optimize_regular_isd_enum
        from p_ary_algebraic_rsd_estimator import optimize_one_round_guessing
        from p_ary_linearization_wagner_optimizer import optimize_hybrid
        isd=optimize_p_ary_regular_isd(P,ELL,R,M,top_k=1,verbose=False)[0]
        results['Regular-ISD']=(isd.log2_work,'m0='+str(isd.w0)+', lambda='+str(isd.lam)+', x='+str(isd.x))
        combo=[v for v in optimize_hybrid(P,ELL,R,M,top_k=4,verbose=False) if v.h>0]
        if combo:
            best=min(combo,key=lambda x:x.time_exponent)
            results['Linearization + Wagner']=(best.time_exponent,'h='+str(best.h)+', rho='+str(best.rho)+', nu='+str(best.nu))
        enum=optimize_regular_isd_enum(P,ELL,R,M,top_k=1,verbose=False)[0]
        results['Regular-ISD Enum']=(enum.work_exponent,'lambda='+str(enum.lam)+', u='+str(enum.u)+', R_U='+str(enum.R_U))
        alg=optimize_one_round_guessing(P,ELL,R,M)[0]
        results['Algebraic RSD']=(alg.total_exponent_omega2,'g='+str(alg.guessed_zero_positions_per_block)+', D='+str(alg.solving_degree))
        from p_ary_regular_isd_rep_fixed_profile import optimize_fixed_profile_rep
        rep=optimize_fixed_profile_rep(P,ELL,R,M,297,122,0,tau_slack=8,top_k=1)[0]
        results['Representation attack']=(rep.work_exponent,'fixed profile: lambda=297, u=122, R_U=0, tau_slack=8; full scan not rerun')
    return results


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--quick',action='store_true')
    ap.add_argument('--output',default='security_estimates.csv')
    args=ap.parse_args()
    calculated=run(args.quick)
    reference=Path(__file__).with_name('reference_table1.csv')
    with reference.open(newline='',encoding='utf-8') as fh:
        rows=list(csv.DictReader(fh))
    output=[]
    for row in rows:
        name=row['attack']
        expected=float(row['paper_log2_cost'])
        if name in calculated:
            value,details=calculated[name]
            status='fixed-profile rerun only' if name=='Representation attack' else 'recomputed'
            output.append([row['goal'],name,row['measure'],expected,f'{value:.9f}',f'{value-expected:+.9f}',status,details])
        else:
            reason='separate optimization workflow' if name=='Representation attack' else 'independent estimator not included' if name=='Rep-MO free-NN benchmark' else 'not evaluated in quick mode'
            output.append([row['goal'],name,row['measure'],expected,'','',reason,''])
    target=Path(args.output)
    target.parent.mkdir(parents=True,exist_ok=True)
    with target.open('w',newline='',encoding='utf-8') as fh:
        writer=csv.writer(fh)
        writer.writerow(['goal','attack','measure','paper_log2_cost','recomputed_log2_cost','difference_bits','status','optimization'])
        writer.writerows(output)
    for item in output:
        print(f'{item[1]:36s} {str(item[4]):>15s}  {item[6]}')
    print('Output:',target)


if __name__=='__main__':
    main()
