#import public_values_aux
#from public_values_aux import *
##################################################################################################################
from sage.all import ZZ, randint

p = None

def generate_distortion_map(E):
    if E.a_invariants() != (0,6,0,1,0):
        raise NotImplementedError
    return E.isogeny(E.lift_x(ZZ(1)), codomain=E)

def generate_torsion_points(E, a, b):
    def get_l_torsion_basis(E, l):
        n = (p+1) // l
        return (n*G for G in E.gens())

    P2, Q2 = get_l_torsion_basis(E, 2**a)
    P3, Q3 = get_l_torsion_basis(E, 3**b)

    return P2, Q2, P3, Q3

def check_torsion_points(E, a, b, P2, Q2, P3, Q3):
    # Make sure Torsion points are
    # generated correctly
    infty = E(0)
    assert 2**(a-1)*P2 != infty
    assert 3**(b-1)*P3 != infty
    assert P2.weil_pairing(Q2, 2**a)**(2**(a-1)) != 1
    assert P3.weil_pairing(Q3, 3**b)**(3**(b-1)) != 1

def gen_bob_keypair(E_start, b, P2, Q2, P3, Q3):
    # generate challenge key
    bobs_key = randint(0,3**b)
    K = P3 + bobs_key*Q3
    phi = E_start.isogeny(K, algorithm="factored")
    EB = phi.codomain()
    EB.set_order((p+1)**2, num_checks=0)

    PB, QB = phi(P2), phi(Q2)

    return bobs_key, EB, PB, QB


import hashlib

set_verbose(-1)
#load('castryck_decru_shortcut.sage')
##################################################################################################################
import time
from itertools import product
#from helpers import possibly_parallel, supersingular_gens, fast_log3

from sage.all import parallel, GF

def possibly_parallel(num_cores):
    if num_cores == 1:
        def _wrap(fun):
            def _fun(args):
                for a in args:
                    yield ((a,), None), fun(a)
            return _fun
        return _wrap
    return parallel(num_cores)

def supersingular_gens(E):
    """
    Compute generators of E, assuming E is supersingular
    with smooth order (p+1)^2 with factors 2 and 3 only.
    This is faster than the PARI method.
    """
    # Find a random point of order (p+1) (probability 1/3)
    p = E.base_ring().characteristic()
    while True:
        P = E.random_point()
        if ((p+1)//2) * P != 0 and ((p+1)//3) * P != 0:
            break

    while True:
        Q = E.random_point()
        if ((p+1)//2) * Q != 0 and ((p+1)//3) * Q != 0:
            # but is it linearly independent? (probability 1/3)
            w = P.weil_pairing(Q, p+1)
            if w**((p+1)/2) != 1 and w**((p+1)//3) != 1:
                return P, Q

def fast_log3(x, base):
    """
    Fast discrete log when elements are known to have order
    dividing 3^k
    """
    one = x.parent().one()
    powers = [base]
    b = base
    log_order = None
    for i in range(10_000):
        b = b**3
        if b.is_one():
            log_order = i+1
            break
        powers.append(b)
    if not b.is_one():
        raise Exception("impossible")
    digits = []
    #assert x**(3**log_order) == 1
    #assert base**(3**(log_order-1)) != 1
    for i in range(log_order):
        for d in range(3):
            if (x * powers[i]**d)**(3**(log_order-i-1)) == 1:
                digits.append((-d) % 3)
                if d:
                    x /= powers[i]**(3-d)
                break
        if x == 1:
            break
    #assert x == 1
    dlog = sum(d*3**i for i, d in enumerate(digits))
    return dlog

def test_fast_log3():
    K = GF(70 * 3**69 + 1)
    g = K.multiplicative_generator()
    g = g**70
    for _ in range(1000):
        r = K.random_element()**70
        dl = fast_log3(r, g)
        assert r == g**dl



#load('richelot_aux.sage')
set_verbose(-1)

def FromProdToJac(C, E, P_c, Q_c, P, Q, a):
    Fp2 = C.base()
    Rx.<x> = Fp2[]

    P_c2 = 2^(a-1)*P_c
    Q_c2 = 2^(a-1)*Q_c
    P2 = 2^(a-1)*P
    Q2 = 2^(a-1)*Q

    a1, a2, a3 = P_c2[0], Q_c2[0], (P_c2 + Q_c2)[0]
    b1, b2, b3 = P2[0], Q2[0], (P2 + Q2)[0]

    # Compute coefficients
    M = Matrix(Fp2, [
        [a1*b1, a1, b1],
        [a2*b2, a2, b2],
        [a3*b3, a3, b3]])
    R, S, T = M.inverse() * vector(Fp2, [1,1,1])
    RD = R * M.determinant()
    da = (a1 - a2)*(a2 - a3)*(a3 - a1)
    db = (b1 - b2)*(b2 - b3)*(b3 - b1)

    s1, t1 = - da / RD, db / RD
    s2, t2 = -T/R, -S/R

    a1_t = (a1 - s2) / s1
    a2_t = (a2 - s2) / s1
    a3_t = (a3 - s2) / s1
    h = s1 * (x^2 - a1_t) * (x^2 - a2_t) * (x^2 - a3_t)

    H = HyperellipticCurve(h)
    J = H.jacobian()

    def isogeny(pair):
        # Argument members may be None to indicate the zero point.

        # The projection maps are:
        # H->C: (xC = s1/x²+s2, yC = s1 y)
        # so we compute Mumford coordinates of the divisor f^-1(P_c): a(x), y-b(x)
        Pc, P = pair
        if Pc:
            xPc, yPc = Pc.xy()
            JPc = J([s1 * x^2 + s2 - xPc, Rx(yPc / s1)])
        # Same for E
        # H->E: (xE = t1 x² + t2, yE = t1 y/x^3)
        if P:
            xP, yP = P.xy()
            JP = J([(xP - t2) * x^2 - t1, yP * x^3 / t1])
        if Pc and P:
            return JPc + JP
        if Pc:
            return JPc
        if P:
            return JP

    imPcP = isogeny((P_c, P))
    imQcQ = isogeny((Q_c, Q))

    # Validate result, for debugging
    # def projC(_x, _y):
    #     return (s1 * _x^2 + s2, s1 * _y)
    # def projE(_x, _y):
    #     return (t1 / _x^2 + t2, t1 * _y / _x^3)
    # Fp4 = Fp2.extension(2)
    # E4 = E.change_ring(Fp4)
    # C4 = C.change_ring(Fp4)
    # divP = [(xr, imPcP[1](xr)) for xr, _ in imPcP[0].roots(Fp4)]
    # assert 2*E4(P) == sum(E4(*projE(*pt)) for pt in divP)
    # assert 2*C4(P_c) == sum(C4(*projC(*pt)) for pt in divP)
    # divQ = [(xr, imQcQ[1](xr)) for xr, _ in imQcQ[0].roots(Fp4)]
    # assert 2*E4(Q) == sum(E4(*projE(*pt)) for pt in divQ)
    # assert 2*C4(Q_c) == sum(C4(*projC(*pt)) for pt in divQ)

    return h, imPcP[0], imPcP[1], imQcQ[0], imQcQ[1], isogeny

class RichelotCorr:
    """
    The Richelot correspondance between hyperelliptic
    curves y²=g1*g2*g3 and y²=h1*h2*h3=hnew(x)

    It is defined by equations:
        g1(x1) h1(x2) + g2(x1) h2(x2) = 0
    and y1 y2 = g1(x1) h1(x2) (x1 - x2)

    Given a divisor D in Mumford coordinates:
        U(x) = x^2 + u1 x + u0 = 0
        y = V(x) = v1 x + v0
    Let xa and xb be the symbolic roots of U.
    Let s, p by the sum and product (s=-u1, p=u0)

    Then on x-coordinates, the image of D is defined by equation:
        (g1(xa) h1(x) + g2(xa) h2(x))
      * (g1(xb) h1(x) + g2(xb) h2(x))
    which is a symmetric function of xa and xb.
    This is a non-reduced polynomial of degree 4.

    Write gred = g-U = g1*x + g0
    then gred(xa) gred(xb) = g1^2*p + g1*g0*s + g0^2
    and  g1red(xa) g2red(xb) + g1red(xb) g2red(xa)
       = 2 g11 g21 p + (g11*g20+g10*g21) s + 2 g10*g20

    On y-coordinates, the image of D is defined by equations:
           V(xa) y = Gred1(xa) h1(x) (xa - x)
        OR V(xb) y = Gred1(xb) h1(x) (xb - x)
    If we multiply:
    * y^2 has coefficient V(xa)V(xb)
    * y has coefficient h1(x) * (V(xa) Gred1(xb) (x-xb) + V(xb) Gred1(xa) (x-xa))
      (x-degree 3)
    * 1 has coefficient Gred1(xa) Gred1(xb) h1(x)^2 (x-xa)(x-xb)
                      = Gred1(xa) Gred1(xb) h1(x)^2 U(x)
      (x-degree 4)
    """
    def __init__(self, G1, G2, H1, H2, hnew):
        assert G1[2].is_one() and G2[2].is_one()
        self.G1 = G1
        self.G2 = G2
        self.H1 = H1
        self.H11 = H1*H1
        self.H12 = H1*H2
        self.H22 = H2*H2
        self.hnew = hnew
        self.x = hnew.parent().gen()

    def map(self, D):
        "Computes (non-monic) Mumford coordinates for the image of D"
        U, V = D
        if not U[2].is_one():
            U = U / U[2]
        V = V  % U
        # Sum and product of (xa, xb)
        s, p = -U[1], U[0]
        # Compute X coordinates (non reduced, degree 4)
        g1red = self.G1 - U
        g2red = self.G2 - U
        assert g1red[2].is_zero() and g2red[2].is_zero()
        g11, g10 = g1red[1], g1red[0]
        g21, g20 = g2red[1], g2red[0]
        # see above
        Px = (g11*g11*p + g11*g10*s + g10*g10) * self.H11 \
           + (2*g11*g21*p + (g11*g20+g21*g10)*s + 2*g10*g20) * self.H12 \
           + (g21*g21*p + g21*g20*s + g20*g20) * self.H22

        # Compute Y coordinates (non reduced, degree 3)
        assert V[2].is_zero()
        v1, v0 = V[1], V[0]
        # coefficient of y^2 is V(xa)V(xb)
        Py2 = v1*v1*p + v1*v0*s + v0*v0
        # coefficient of y is h1(x) * (V(xa) Gred1(xb) (x-xb) + V(xb) Gred1(xa) (x-xa))
        # so we need to symmetrize:
        # V(xa) Gred1(xb) (x-xb)
        # = (v1*xa+v0)*(g11*xb+g10)*(x-xb)
        # = (v1*g11*p + v1*g10*xa + v0*g11*xb + v0*g10)*x
        # - xb*(v1*g11*p + v1*g10*xa + v0*g11*xb + v0*g10)
        # Symmetrizing xb^2 gives u1^2-2*u0
        Py1 = (2*v1*g11*p + v1*g10*s + v0*g11*s + 2*v0*g10)*self.x \
          - (v1*g11*s*p + 2*v1*g10*p + v0*g11*(s*s-2*p) + v0*g10*s)
        Py1 *= self.H1
        # coefficient of 1 is Gred1(xa) Gred1(xb) h1(x)^2 U(x)
        Py0 = self.H11 * U * (g11*g11*p + g11*g10*s + g10*g10)

        # Now reduce the divisor, and compute Cantor reduction.
        # Py2 * y^2 + Py1 * y + Py0 = 0
        # y = - (Py2 * hnew + Py0) / Py1
        _, Py1inv, _ = Py1.xgcd(Px)
        Py = (- Py1inv * (Py2 * self.hnew + Py0)) % Px
        assert Px.degree() == 4
        assert Py.degree() <= 3

        Dx = ((self.hnew - Py ** 2) // Px)
        Dy = (-Py) % Dx
        return (Dx, Dy)

def jacobian_double(h, u, v):
    """
    Computes the double of a jacobian point (u,v)
    given by Mumford coordinates: except that u is not required
    to be monic, to avoid redundant reduction during repeated doubling.

    See SAGE cantor_composition() and cantor_reduction
    """
    assert u.degree() == 2
    # Replace u by u^2
    # Compute h3 the inverse of 2*v modulo u
    # Replace v by (v + h3 * (h - v^2)) % u
    q, r = u.quo_rem(2*v)
    if r[0] == 0: # gcd(u, v) = v, very improbable
        a = q**2
        b = (v + (h - v^2) // v) % a
        return a, b
    else: # gcd(u, v) = 1
        h3 = 1 / (-r[0]) * q
        a = u*u
        b = (v + h3 * (h - v**2)) % a
        # Cantor reduction
        Dx = (h - b**2) // a
        Dy = (-b) % Dx
        return Dx, Dy

def jacobian_iter_double(h, u, v, n):
    for _ in range(n):
        u, v = jacobian_double(h, u, v)
    return u.monic(), v

def FromJacToJac(h, D11, D12, D21, D22, a, powers=None):
    # power is an optional list of precomputed tuples
    # (l, 2^l D1, 2^l D2) where l < a are increasing
    R,x = h.parent().objgen()
    Fp2 = R.base()

    #J = HyperellipticCurve(h).jacobian()
    D1 = (D11, D12)
    D2 = (D21, D22)

    next_powers = None
    if not powers:
        # Precompute some powers of D1, D2 to save computations later.
        # We are going to perform O(a^1.5) squarings instead of O(a^2)
        if a >= 16:
            gap = Integer(a).isqrt()
            doubles = [(0, D1, D2)]
            _D1, _D2 = D1, D2
            for i in range(a-1):
                _D1 = jacobian_double(h, _D1[0], _D1[1])
                _D2 = jacobian_double(h, _D2[0], _D2[1])
                doubles.append((i+1, _D1, _D2))
            _, (G1, _), (G2, _) = doubles[a-1]
            G1, G2 = G1.monic(), G2.monic()
            next_powers = [doubles[a-2*gap], doubles[a-gap]]
        else:
            G1, _ = jacobian_iter_double(h, D1[0], D1[1], a-1)
            G2, _ = jacobian_iter_double(h, D2[0], D2[1], a-1)
    else:
        (l, _D1, _D2) = powers[-1]
        if a >= 16:
            next_powers = powers if l < a-1 else powers[:-1]
        G1, _ = jacobian_iter_double(h, _D1[0], _D1[1], a-1-l)
        G2, _ = jacobian_iter_double(h, _D2[0], _D2[1], a-1-l)

    #assert 2^a*D1 == 0
    #assert 2^a*D2 == 0
    G3, r3 = h.quo_rem(G1 * G2)
    assert r3 == 0

    delta = Matrix(G.padded_list(3) for G in (G1,G2,G3))
    # H1 = 1/det (G2[1]*G3[0] - G2[0]*G3[1])
    #        +2x (G2[2]*G3[0] - G3[2]*G2[0])
    #        +x^2(G2[1]*G3[2] - G3[1]*G2[2])
    # The coefficients correspond to the inverse matrix of delta.
    delta = delta.inverse()
    H1 = -delta[0][0]*x^2 + 2*delta[1][0]*x - delta[2][0]
    H2 = -delta[0][1]*x^2 + 2*delta[1][1]*x - delta[2][1]
    H3 = -delta[0][2]*x^2 + 2*delta[1][2]*x - delta[2][2]

    hnew = H1*H2*H3

    # Now compute image points: Richelot isogeny is defined by the degree 2
    R = RichelotCorr(G1, G2, H1, H2, hnew)

    imD1 = R.map(D1)
    imD2 = R.map(D2)
    if next_powers:
        next_powers = [(l, R.map(_D1), R.map(_D2))
            for l, _D1, _D2 in next_powers]
    return hnew, imD1[0], imD1[1], imD2[0], imD2[1], R.map, next_powers

def FromJacToProd(G1, G2, G3):
    """
    Construct the "split" isogeny from Jac(y^2 = G1*G2*G3)
    to a product of elliptic curves.

    This computation is the same as Benjamin Smith
    see 8.3 in http://iml.univ-mrs.fr/~kohel/phd/thesis_smith.pdf
    """
    h = G1*G2*G3
    R = h.parent()
    Fp2 = R.base()
    x = R.gen()

    M = Matrix(G.padded_list(3) for G in (G1,G2,G3))
    # Find homography
    u, v, w = M.right_kernel().gen()
    d = u/2
    (ad, _), (b, _) = (x^2 - v*x + w*d/2).roots()
    a = ad/d

    # Apply transform G(x) -> G((a*x+b)/(x+d))*(x+d)^2
    # The coefficients of x^2 are M * (1, a, a^2)
    # The coefficients of 1 are M * (d^2, b*d, b^2)
    H11, H21, H31 = M * vector([1, a, a*a])
    H10, H20, H30 = M * vector([d*d, b*d, b*b])
    assert G1((a*x+b)/(x+d))*(x+d)**2 == H11*x^2+H10

    h2 = (H11*x^2+H10)*(H21*x^2+H20)*(H31*x^2+H30)
    H2 = HyperellipticCurve(h2)

    p1 = (H11*x+H10)*(H21*x+H20)*(H31*x+H30)
    p2 = (H11+H10*x)*(H21+H20*x)*(H31+H30*x)
    # We will need to map to actual elliptic curve
    p1norm = (x + H10*H21*H31)*(x + H20*H11*H31)*(x + H30*H11*H21)
    p2norm = (x + H11*H20*H30)*(x + H21*H10*H30)*(x + H31*H10*H20)
    E1 = EllipticCurve([0, p1norm[2], 0, p1norm[1], p1norm[0]])
    E2 = EllipticCurve([0, p2norm[2], 0, p2norm[1], p2norm[0]])

    def morphE1(x, y):
        # from y^2=p1 to y^2=p1norm
        return (H11*H21*H31*x, H11*H21*H31*y)
    def morphE2(x, y):
        # from y^2=p1 to y^2=p2norm
        return (H10*H20*H30*x, H10*H20*H30*y)
    # The morphisms are:
    # inverse homography:
    # H->H2: x, y => ((b-dx) / (x-a), y/(x-a)^3)
    # then H2->E1:(x,y) => (x^2,y)
    #   or H2->E2:(x,y) => (1/x^2,y/x^3)

    def isogeny(D):
        HyperellipticCurve(h).jacobian()(D)
        # To map a divisor, perform the change of coordinates
        # on Mumford coordinates
        U, V = D
        # apply homography
        # y = v1 x + v0 =>
        U_ = U[0] * (x+d)^2 + U[1]*(a*x+b)*(x+d) + U[2]*(a*x+b)^2
        V_ = V[0] * (x+d)^3 + V[1]*(a*x+b)*(x+d)^2
        V_ = V_ % U_
        v1, v0 = V_[1], V_[0]
        # prepare symmetric functions
        s = - U_[1] / U_[2]
        p = U_[0] / U_[2]
        # compute Mumford coordinates on E1
        # Points x1, x2 map to x1^2, x2^2
        U1 = x^2 - (s*s - 2*p)*x + p^2
        # y = v1 x + v0 becomes (y - v0)^2 = v1^2 x^2
        # so 2v0 y-v0^2 = p1 - v1^2 xH^2 = p1 - v1^2 xE1
        V1 = (p1 - v1^2 * x + v0^2) / (2*v0)
        # Reduce Mumford coordinates to get a E1 point
        V1 = V1 % U1
        U1red = (p1 - V1**2) // U1
        xP1 = -U1red[0] / U1red[1]
        yP1 = V1(xP1)
        assert yP1**2 == p1(xP1)
        # Same for E2
        # Points x1, x2 map to 1/x1^2, 1/x2^2
        U2 = x^2 - (s*s-2*p)/p^2*x + 1/p^2
        # yE = y1/x1^3, xE = 1/x1^2
        # means yE = y1 x1 xE^2
        # (yE - y1 x1 xE^2)(yE - y2 x2 xE^2) = 0
        # p2 - yE (x1 y1 + x2 y2) xE^2 + (x1 y1 x2 y2 xE^4) = 0
        V21 = x^2 * (v1 * (s*s-2*p) + v0*s)
        V20 = p2 + x^4 * (p*(v1^2*p + v1*v0*s + v0^2))
        # V21 * y = V20
        _, V21inv, _ = V21.xgcd(U2)
        V2 = (V21inv * V20) % U2
        #assert V2**2 % U2 == p2 % U2
        # Reduce coordinates
        U2red = (p2 - V2**2) // U2
        xP2 = -U2red[0] / U2red[1]
        yP2 = V2(xP2)
        #assert yP2**2 == p2(xP2)

        return E1(morphE1(xP1, yP1)), E2(morphE2(xP2, yP2))

    return isogeny, (E1, E2)

def Does22ChainSplit(C, E, P_c, Q_c, P, Q, a):
    """
    Returns None if the chain does not split
    or a tuple (chain of isogenies, codomain (E1, E2))
    """
    chain = []
    # gluing step
    h, D11, D12, D21, D22, f = FromProdToJac(C, E, P_c, Q_c, P, Q, a)
    chain.append(f)
    next_powers = None
    # print(f"order 2^{a-1} on hyp curve ...")
    for i in range(1,a-2+1):
        h, D11, D12, D21, D22, f, next_powers = FromJacToJac(
            h, D11, D12, D21, D22, a-i, powers=next_powers)
        chain.append(f)
        # print(f"order 2^{a - i - 1} on hyp curve {h}")
    # now we are left with a quadratic splitting: is it singular?
    G1 = D11
    G2 = D21
    G3, r3 = h.quo_rem(G1 * G2)
    assert r3 == 0

    delta = Matrix(G.padded_list(3) for G in (G1,G2,G3))
    if delta.determinant():
        return None

    # Finish chain
    f, codomain = FromJacToProd(G1, G2, G3)
    chain.append(f)
    return chain, codomain

def OddCyclicSumOfSquares(n, factexpl, provide_own_fac):
    return NotImplemented

def Pushing3Chain(E, P, i):
    """
    Compute chain of isogenies quotienting
    out a point P of order 3^i

    https://trac.sagemath.org/ticket/34239
    """
    def rec(Q, k):
        assert k
        if k == 1:  # base case
#            assert Q and not 3*Q
            return [EllipticCurveIsogeny(Q.curve(), Q, degree=3, check=False)]

        k1 = int(k * .8 + .5)
        k1 = max(1, min(k-1, k1))  # clamp to [1, k-1]

        Q1 = 3^k1 * Q
        L = rec(Q1, k-k1)

        Q2 = Q
        for psi in L:
            Q2 = psi(Q2)
        R = rec(Q2, k1)

        return L + R

    chain = rec(P, i)
    return chain[-1].codomain(), chain

def AuxiliaryIsogeny(i, u, v, E_start, P2, Q2, tauhatkernel, two_i):
    """
    Compute the distored  kernel using precomputed u,v and the
    automorphism two_i.

    This is used to construct the curve C from E_start and we
    compute the image of the points P_c and Q_c
    """
    tauhatkernel_distort = u*tauhatkernel + v*two_i(tauhatkernel)

    C, tau_tilde = Pushing3Chain(E_start, tauhatkernel_distort, i)
    def chain(P):
        Pc = u*P + v*two_i(P)
        for taut in tau_tilde:
            Pc = taut(Pc)
        return Pc
    return C, chain(P2), chain(Q2), chain

#load('uvtable.sage')
uvtable =  [[ 1, 3, 1, 1 ],
            [ 3, 5, 1, 1 ],
            [ 5, 8, 3, 1 ],
            [ 7, 13, 23, 37 ],
            [ 9, 15, 59, 49 ],
            [ 11, 19, 385, 223 ],
            [ 13, 21, 125, 349 ],
            [ 15, 24, 825, 661 ],
            [ 17, 29, 1307, 10075 ],
            [ 19, 34, 48991, 58347 ],
            [ 21, 41, 1440605, 168241 ],
            [ 23, 40, 721143, 348325 ],
            [ 25, 41, 956405, 330539 ],
            [ 27, 44, 3038895, 427699 ],
            [ 29, 46, 1021891, 416565 ],
            [ 31, 51, 16963049, 18346535 ],
            [ 33, 53, 37852565, 22446169 ],
            [ 35, 58, 111188129, 237611043 ],
            [ 37, 61, 1046252867, 436151935 ],
            [ 39, 63, 2170653479, 338777345 ],
            [ 41, 70, 5096872085, 16719304107 ],
            [ 43, 71, 3450988735, 22477861057 ],
            [ 45, 72, 36322560147, 10591569769 ],
            [ 47, 75, 86165183959, 30682562545 ],
            [ 49, 81, 1191966366037, 435249495185 ],
            [ 51, 82, 894987407119, 685749016857 ],
            [ 53, 86, 5245386911165, 2760159548823 ],
            [ 55, 91, 32934192159529, 17441114172845 ],
            [ 57, 102, 2190114350879525, 260974849403823 ],
            [ 59, 113, 28891668768966497, 48861669697289023 ],
            [ 61, 97, 50681358988013, 84726397973135 ],
            [ 63, 101, 78659490242153, 588335068566473 ],
            [ 65, 105, 1596013502467285, 2632323529050329 ],
            [ 67, 114, 70412980307308399, 62686701490894407 ],
            [ 69, 110, 12892817990595629, 8623576557380355 ],
            [ 71, 115, 114484881824008489, 72322403491313995 ],
            [ 73, 116, 103635209321564853, 34464817171338499 ],
            [ 75, 122, 464465051177946401, 1059825152048744007 ],
            [ 77, 124, 244343193203932323, 1983276534366384091 ],
            [ 79, 128, 6343381291216761945, 7917926984230115629 ],
            [ 81, 130, 28566473980265585195, 5041317877686482943 ],
            [ 83, 137, 181720453697144894479, 185210292760308661399 ],
            [ 85, 142, 440609178211339916669, 1155977109003558234825 ],
            [ 87, 138, 135632717076042607049, 41215894556701764267 ],
            [ 89, 161, 1222956779072715620275163, 597364436893573685253665 ],
            [ 91, 146, 1372152330932529621391, 3909484878809987832603 ],
            [ 93, 149, 21378440155985573227517, 2287527404838860311835 ],
            [ 95, 158, 350624537116384590475369, 245110662843133703255463 ],
            [ 97, 154, 40647358321638009263339, 22889402686395599236455 ],
            [ 99, 157, 103259710456658502419009, 7626105691954967759659 ],
            [ 101, 163, 1455730063152724038426397, 1416574258526936122877257 ],
            [ 103, 166, 6472464613771489156182361, 3071160755841729319913727 ],
            [ 105, 173, 48156682801112493746804443, 48806553292231961540901385 ],
            [ 107, 171, 15045109205299947458742431, 20246415759421339975812665 ],
            [ 109, 173, 40086080134979817159324797, 7442308980728933711310925 ],
            [ 111, 176, 28743643831152551428816905, 30237363386678939503444921 ],
            [ 113, 181, 1393839104879662393660244885, 274100983423088393617256351 ],
            [ 115, 186, 8896248528986977827604563329, 1698629786845835747572254477 ],
            [ 117, 198, 626835937715839625262818909741, 46756449596867722030056278805 ],
            [ 119, 201, 834061720109383975041487202951, 793350195710074077993481130689 ],
            [ 121, 194, 121426266556241448578060029909, 35259884543259741522564297645 ],
            [ 123, 196, 166845741627362883159627652065, 77583581009954222648132290111 ],
            [ 125, 199, 571125018018313343591937315133, 100761764876203925419739234917 ],
            [ 127, 204, 2576375767745793714986473660425, 1945715490867257765804502708449 ],
            [ 129, 205, 2952735297854353799630528576395, 1353958819894174241984626701841 ],
            [ 131, 215, 197545494326630861738405078137825, 57692262310310525777165490877507 ],
            [ 133, 220, 1289262252923088954234660529683597, 70594785629332282040862555600869 ],
            [ 135, 216, 246599812686791521573601328629577, 68402650496677101758628224525965 ],
            [ 137, 220, 491073477706829402358064079515557, 550403784313436243605443020108921 ],
            [ 139, 227, 13947464794839242415031743999011825, 2182842373290636339539010270272797 ],
            [ 141, 227, 11210408395463674365571416690467491, 4219269916039645039197877131072581 ],
            [ 143, 230, 18766548510858109336269699668811769, 17349906207732399623195773404253797 ],
            [ 145, 234, 21163932112914320351694650766663371, 80056990648089193490869352887919415 ],
            [ 147, 235, 30523709291265186212877840772712015, 100721145647157454807990914051304217 ],
            [ 149, 237, 188903207236680802204610538062762285, 124340225169979360970931762395241179 ],
            [ 151, 241, 1064613718783959431437571858035020359, 567962653752070279035499919615098559 ],
            [ 153, 246, 8634384301732447160246368738270232645, 2670951645943092026464943487647622777 ],
            [ 155, 246, 3170652727305442454640890581696763761, 1810937020240578537610222609406499003 ],
            [ 157, 265, 4020299292113727584761335277856159377475, 3283364666257731609856239362369744140181 ],
            [ 159, 258, 66108437664204525806786184799441078951, 335974533286347598561225627287294077163 ],
            [ 161, 260, 1335795878778890348287306117055330366283, 26364976179932208434095842120430657361 ],
            [ 163, 260, 941941024888040758249411735616150541855, 306406340503614483695656712833569423859 ],
            [ 165, 271, 45403924326750553804216238826423009797347, 20781301123222809604782614270666346368407 ],
            [ 167, 268, 14698786480566420842291242108264271021463, 7253442290547392057745893373384581067115 ],
            [ 169, 279, 962981036477721177168087165895489744962469, 104369471276049320600285425376864198248969 ],
            [ 171, 272, 51559390602507848672541919606277314763055, 16278585368855546886938054876033893347659 ],
            [ 173, 275, 68800906901399611280752468576822802281661, 72703070741555003483807766364271033071709 ],
            [ 175, 279, 155509200245001088454141422472334051336185, 398015171116846292561771477180985259249333 ],
            [ 177, 284, 3502270312087824033080528027982022180913787, 1999713834259911440650698777351999475627411 ],
            [ 179, 284, 953147175900762850002632170954304811030543, 1093362175592097044156999416990608493928345 ],
            [ 181, 287, 948196794328116518443188457994565505680301, 2192629523341781259822209167253453081535659 ],
            [ 183, 295, 110351711607278014205488711138395588314519929, 111156517587317434358862730962113928083076065 ],
            [ 185, 294, 108640186370365588968519288494961396068002229, 19460867532647681757917130128341553283257355 ],
            [ 187, 305, 6986854561740493118793284241874088541642664639, 2012611159390538283898452182822930997938452759 ],
            [ 189, 314, 14355011411522704500881803497540798664862671405, 91059364818915915525252764228897266082997809313 ],
            [ 191, 312, 89281984020507698736935200600291811745000722055, 9472751708896178153267679256289899285130055709 ],
            [ 193, 310, 2201441366547249280252919810130031245805902475, 22133838334141451434794499995654973063861851663 ],
            [ 195, 311, 47120726179816159974739221695811927540209468929, 14649446757497762798903747600274101603958086635 ],
            [ 197, 321, 2041868972249079925931601652508238160696011349085, 152403753943886925774888434390188711016888324329 ],
            [ 199, 323, 4084087309751054942635828068413903062572115652521, 282661076824221149249716126685415511648751788075 ],
            [ 201, 337, 469027639725904725662203145699663095298951117013163, 122454449800125493373315157656128785085012907213365 ],
            [ 203, 333, 58306584581505435575270544202394717732369685816847, 59353130530335548987441606748227299174850038051267 ],
            [ 205, 326, 8461975385335211102501293139932739660610063315811, 372136930471057220009135104269753467201227105515 ],
            [ 207, 329, 17109965355729072634053235569737005657412037023801, 7415804984047900895099521297803491897985884057909 ],
            [ 209, 336, 338508439585400762476494905080788999516925316046987, 71007046432952698440311422929325986481851511566311 ],
            [ 211, 337, 479551890567094355355633250786065788805458424781169, 27135565860860992904742773910364565239188585864521 ],
            [ 213, 345, 3027123739672472290120792668493018552962973630937155, 3939697930134191444848561569777855318731399611623239 ],
            [ 215, 343, 3725675086000635662248770427177748214509736155568505, 237714464588099969476803392745335436140702284180337 ],
            [ 217, 344, 671339668995449793878135961271332008274669385373973, 520525000640529464008402481498951294642334542604109 ],
            [ 219, 348, 4716683201639743233103934487580879813439727625180335, 7784835406196643680909654680655323002345184257781421 ],
            [ 221, 361, 619292899875594502460526319390862407579892910134713075, 1038121266227125796019309557927545340275022353819350841 ],
            [ 223, 368, 17304742317011861510839306512138034050055067709140501127, 8685444559529848308731502054942255687130975746690812435 ],
            [ 225, 358, 557307356100144816366509076411054492963471250077498101, 113459738725765935533319529458088433015606278936624095 ],
            [ 227, 360, 482281387455498677223543258915925727763417320356900335, 150401031029209333206912754676206274165276998351837271 ],
            [ 229, 366, 10285426977742533088616763662572526259868679357687803325, 2563568259921525261331366312875178507900471934923113183 ],
            [ 231, 372, 59444399801298482773383410097965509640549890645535007543, 38477042040337240938859340580233872542489790413670865635 ],
            [ 233, 370, 29081533084346872777805946256092421816362024443880111515, 4544441295116780113103824480646073302288147406047324487 ],
            [ 235, 383, 2820218901779648501547551432212738253654681846157049028785, 1712752124942388181908296892310624395666760274039553940963 ],
            [ 237, 384, 5016709389489849249430681050365491718445406943961172353213, 1878498828415162095700645548569999903048067008153094878461 ],
            [ 239, 380, 679707664933593347121549332185624094242006572416905994505, 480678566760659095403467426158904358036842167708634826311 ]]

#load('speedup.sage')
# Don't pollute the global namespace
def _do_speedup():
    # And because why not
    proof.all(False)

    # Lorenz Panny has fixed both of the below monkey patches with the tickets:
    # - https://trac.sagemath.org/ticket/34281 (Caching of the finite fields)
    # - https://trac.sagemath.org/ticket/34284 (Dimension of hyperelliptic curve)
    #
    # We should check the version of sage and if >= 9.7 skip the below patches
    from sage.misc.banner import require_version
    if not require_version(9,7):
        # Since this type gets created before we could ever hope to monkey patch the
        # `sage.categories.fields.Fields.ParentMethods`
        # method, we'll patch it on the relevant type instead.
        # We'll patch a few different types to make sure we get the relevant things (large and small prime, extension and no extension)
        p = 2^127 - 1 # Arbitrary large prime
        to_patch = [GF(3), GF(3^2), GF(p), GF(p^2)]
        for x in to_patch:
            type(x).vector_space = sage.misc.cachefunc.cached_method(type(x).vector_space)

        # An alternative would be to replace the bytecode in
        # `sage.categories.fields.Fields.ParentMethods.vector_space`
        # as all types share the same method, by identity
        # Something to be explored later, perhaps :)

        # No use calculating the dimension of HyperElliptic every single time
        from sage.schemes.projective.projective_subscheme import AlgebraicScheme_subscheme_projective
        AlgebraicScheme_subscheme_projective.dimension = lambda self: 1


_do_speedup()


# ===================================
# =====  ATTACK  ====================
# ===================================


def CastryckDecruAttack(E_start, P2, Q2, EB, PB, QB, two_i, num_cores=1):
    tim = time.time()

    skB = [] # TERNARY DIGITS IN EXPANSION OF BOB'S SECRET KEY

    # gathering the alpha_i, u, v from table
    expdata = [[0, 0, 0] for _ in range(b-3)]
    for i in range(b%2, b-3, 2):
        index = (b-i) // 2
        row = uvtable[index-1]
        if row[1] <= a:
            expdata[i] = row[1:4]

    # gather digits until beta_1
    bet1 = 0
    while not expdata[bet1][0]:
        bet1 += 1
    bet1 += 1

    ai,u,v = expdata[bet1-1]

    print(f"Determination of first {bet1} ternary digits. We are working with 2^{ai}-torsion.")

    bi = b - bet1
    alp = a - ai

    @possibly_parallel(num_cores)
    def CheckGuess(first_digits):
        print(f"Testing digits: {first_digits}")

        scalar = sum(3^k*d for k,d in enumerate(first_digits))
        tauhatkernel = 3^bi * (P3 + scalar*Q3)

        tauhatkernel_distort = u*tauhatkernel + v*two_i(tauhatkernel)

        C, P_c, Q_c, chainC = AuxiliaryIsogeny(bet1, u, v, E_start, P2, Q2, tauhatkernel, two_i)
        # We have a diagram
        #  C <- Eguess <- E_start
        #  |    |
        #  v    v
        #  CB-> EB
        split = Does22ChainSplit(C, EB, 2^alp*P_c, 2^alp*Q_c, 2^alp*PB, 2^alp*QB, ai)
        if split:
            Eguess, _ = Pushing3Chain(E_start, tauhatkernel, bet1)

            chain, (E1, E2) = split
            # Compute the 3^b torsion in C
            P3c = chainC(P3)
            Q3c = chainC(Q3)
            # Map it through the (2,2)-isogeny chain
            if E2.j_invariant() == Eguess.j_invariant():
                CB, index = E1, 0
            else:
                CB, index = E2, 1
            def apply_chain(c, X):
                X = (X, None) # map point to C x {O_EB}
                for f in c:
                    X = f(X)
                return X[index]
            print("Computing image of 3-adic torsion in split factor CB")
            P3c_CB = apply_chain(chain, P3c)
            Q3c_CB = apply_chain(chain, Q3c)

            Z3 = Zmod(3^b)
            # Determine kernel of the 3^b isogeny.
            # The projection to CB must have 3-adic rank 1.
            # To compute the kernel we choose a symplectic basis of the
            # 3-torsion at the destination, and compute Weil pairings.
            CB.set_order((p+1)^2, num_checks=1) # keep sanity check
            P_CB, Q_CB = supersingular_gens(CB)
            P3_CB = ((p+1) / 3^b) * P_CB
            Q3_CB = ((p+1) / 3^b) * Q_CB
            w = P3_CB.weil_pairing(Q3_CB, 3^b)
            # Compute kernel
            for G in (P3_CB, Q3_CB):
                xP = fast_log3(P3c_CB.weil_pairing(G, 3^b), w)
                xQ = fast_log3(Q3c_CB.weil_pairing(G, 3^b), w)
                if xQ % 3 != 0:
                    sk = int(-Z3(xP) / Z3(xQ))
                    return sk

            return True

    guesses = [ZZ(i).digits(3, padto=bet1) for i in range(3^bet1)]

    for result in CheckGuess(guesses):
        ((first_digits,), _), sk = result
        if sk is not None:
            print("Glue-and-split! These are most likely the secret digits.")
            bobskey = sk
            break

    # Sanity check
    bobscurve, _ = Pushing3Chain(E_start, P3 + bobskey*Q3, b)
    found = bobscurve.j_invariant() == EB.j_invariant()

    if found:
        print(f"Bob's secret key revealed as: {bobskey}")
        print(f"In ternary, this is: {Integer(bobskey).digits(base=3)}")
        print(f"Altogether this took {time.time() - tim} seconds.")
        return bobskey
    else:
        print("Something went wrong.")
        print(f"Altogether this took {time.time() - tim} seconds.")
        return None


#load('sandwich_attack.sage')
##################################################################################################################

SIKE_parameters = {
    "SIKEp434" : (216, 137),
    "SIKEp503" : (250, 159),
    "SIKEp610" : (305, 192),
    "SIKEp751" : (372, 239),
    "SIKEp964" : (486, 301), # removed after NIST round 1
}

# Change me to attack different parameter sets
NIST_submission = "SIKEp434"
a, b = SIKE_parameters[NIST_submission]

print(f"Running the attack against {NIST_submission} parameters, which has a prime: 2^{a}*3^{b} - 1")

print(f"Generating public data for the attack...")
# Set the prime, finite fields and starting curve
# with known endomorphism
p = 2^a*3^b - 1
# public_values_aux.p = p

Fp2.<i> = GF(p^2, modulus=x^2+1)
assert i^2 == -1
R.<x> = PolynomialRing(Fp2)

E_start = EllipticCurve(Fp2, [0,6,0,1,0])
E_start.set_order((p+1)^2, num_checks=0) # Speeds things up in Sage

# Generation of the endomorphism 2i
two_i = generate_distortion_map(E_start)

# $IKEp434 public parameters

xQ2 = 8633131302536015373065425580178973814526244742660764898957635611033517358603093513483897324469034427019598357249425684820405193836 + i*1640555213321637736080614728970921962714590288563692816952785470842808462670732196555713644986698688787353020078064569199240185333
yQ2 = 20276452752220665548202189403598170750834982427130760850813254160550305310659929663123304778814287531500756146204805251963783256037 + i*10045306525245350298803819046509877432229480969314772374869175643233206473596453796721101344057683381390923103776706006170651177942
Q2 = E_start(xQ2, yQ2)

xP2 = 2634539327592482918121599540115765431217195093350648632832477775508933673747596362667240890051240463853167541162279343167040310088 + i*18590308952679468489364793668589003541299106140709579196186461020066893645141198854487503147226318730158493210982567772716162869840
yP2 = 18499992072774772182750461054948965122862326576938683155863157755664308576685791546530637605543615310883354355922717114976263189216 + i*10983718925653566249610333622918370357192097441961014913751641775508865561311331364566791542776619041356373750734992554370506677551
P2 = E_start(xP2, yP2)

# # CONSISTENCY WITH R (NOT NEEDED BUT OK)
# XR2 = 10548244869191429978994573331033429460802791853191679921432716242390096998215982561051229194803656270150791181542353263212179039510 + i*17623338845092751517427595119320347017334966146230013113905734683582704966390296970846105400364294574370981828797535336936167097772
# assert (P2 - Q2)[0] == xR2

xQ3 = 13106015910647201458426811493288965923311702902321179794984306791335898269651901670809619116119997952683697617529379507339288983622 + i*0
yQ3 = 0 + i*10209775938515962501771741506081580425243588708606392462054462399651871393790372518908435424495021346995173633235373991504988757970
Q3 = E_start(xQ3, yQ3)

xP3 = 5822289030790821842647204127346110197186614331916510409554480418611145246532692679762948023941031185216358707524703325193156147113 + i*0
yP3 = 4631002038627486062145710538859886699092897850004224163519174820337269208909673679867855016325656365561668068341925816094377133115 + i*0
P3 = E_start(xP3, yP3)

# # CONSISTENCY WITH R (NOT NEEDED BUT OK)
# # Typo in magma, should be P3 and Q3
# xR3 = 19978714732817982296321998790126652405475699311529669091328949981490769847281914491438519436155586335833863255694913096932863948652 + i*14167827257511306746606440016400170231086622175754382579855491498256779752299521404090563911050166061448571907478184141518856743652
# assert (P3 - Q3)[0] == xR3

# Curve isogeny system "SIDHp434". Base curve: Montgomery curve By^2 = Cx^3 + Ax^2 + Cx defined over GF(p434^2), where A=6, B=1, C=1 and p434 = 2^216*3^137-1

# BOB'S PUBLIC KEY:

# challenge
xPB = 20648630945288875895543631892994042382468428865686818676390481141407070182341828883288180646457486918619949217867858294626861534175 + i * 7241507110606646585814615724269455050671965086273890121488296367344649592019089509293512287506505961438489163984183048554524445177
xQB = 5984770474013541647074824123582552527142702827775518051119219875288895351023018008192421851402725912456828396700943060384651702384 + i * 578644568857744686591928087314403964664806861847276792436523806903077807322095036537673556147556428320152382324190658718235920171
xRB = 16476712615638590366320952765153169972919821954793203742870963905179874505555572071685431005888045559348952324911698539477624609757 + i * 9629745550486482583422035276247659527144888434282679463170379307267488821902602083895745462292248669658520717106515223215336002651

B = (1 - xPB*xQB - xPB*xRB - xQB*xRB)^2/(4*xPB*xQB*xRB) - xPB - xQB - xRB

yPB = sqrt(xPB^3 + B*xPB^2 + xPB)

yQB = sqrt(xQB^3 + B*xQB^2 + xQB)

# SMALL ERROR IN SIDH-spec.pdf, CORRECTED HERE
if xRB + xQB + xPB + B != (yQB + yPB)^2 / (xQB - xPB)^2:
    yQB = -yQB

# let's check:
EB = EllipticCurve(Fp2, [0,B,0,1,0])
EB.set_order((p+1)^2, num_checks=0) # Speeds things up in Sage

PB = EB(xPB, yPB)
QB = EB(xQB, yQB)

# ===================================
# =====  ATTACK  ====================
# ===================================

def RunAttack(num_cores):
    return CastryckDecruAttack(E_start, P2, Q2, EB, PB, QB, two_i, num_cores=num_cores)

if __name__ == '__main__' and '__file__' in globals():
    if '--parallel' in sys.argv:
        # Set number of cores for parallel computation
        num_cores = os.cpu_count()
        print(f"Performing the attack in parallel using {num_cores} cores")
    else:
        num_cores = 1

    if '--sandwich' in sys.argv:
        # Use the fact that 2^(a-1) - 5*3^b is a sum of squares
        assert two_squares(2^(a-1) - 5*3^b)
        recovered_key = SandwichAttack(E_start, P2, Q2, EB, PB, QB, two_i, k=5, alp=1)
    else:
        out_Bob = RunAttack(num_cores)
        print(out_Bob)
        out_Bob = hashlib.sha3_512(str(out_Bob).encode())
        print("\nSHA3-512 hash of Bob's shared secret - SHA3-512:\n")
        print(out_Bob.hexdigest())

