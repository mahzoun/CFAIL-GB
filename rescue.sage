load('CompactFIPS202.sage')
class Rescue:
    def __init__(self, p, m, capacity, security_level, N=None):
        assert is_prime(p), f"Cipher is only defined over prime fields."
        self.p = p
        self.Fp = GF(p)
        self.m = m
        self.rate = m-capacity
        self.capacity = m - self.rate
        self.security_level = security_level
        alpha, alphainv = self._get_alphas()
        self.alpha = alpha
        self.alphainv = alphainv
        self.N = N
        if not N:
            self.N = self._get_number_of_rounds()
        self.MDS = self._get_mds_matrix()
        self.round_constants = self._get_round_constants()

    def __call__(self, input_sequence):
        Fp, rate, capacity = self.Fp, self.rate, self.capacity
        input_sequence = [Fp(elem) for elem in input_sequence]
        if len(input_sequence) % rate == 0:
            return self.rescue_hash(input_sequence)
        return self.rescue_wrapper(input_sequence)

    def _get_alphas(self):
        p = self.p
        alpha = 7
        while gcd(alpha, p-1) != 1:
            alpha += 1
        _, alphainv, _ = xgcd(alpha, p-1)
        return alpha, alphainv % (p-1)

    def _get_number_of_rounds(self):
        p, m, rate, capacity, security_level, alpha = self.p, self.m, self.rate, self.capacity, self.security_level, self.alpha
        # get number of rounds for Groebner basis attack
        dcon = lambda N : floor(0.5 * (alpha-1) * m * (N-1) + 2)
        v = lambda N : m*(N-1) + rate
        target = 2^security_level
        for l1 in range(1, 25):
            if binomial(v(l1) + dcon(l1), v(l1))^2 > target:
                break
        # set a minimum value for sanity and add 50%
        return ceil(1.5 * max(5, l1))

    def _get_mds_matrix(self):
        p, Fp, m = self.p, self.Fp, self.m
        # get a primitive element
        g = Fp(2)
        while g.multiplicative_order() != p-1:
            g = g + 1
        # get a systematic generator matrix for the code
        V = matrix([[g^(i*j) for j in range(2*m)] for i in range(m)])
        V_ech = V.echelon_form()
        # the MDS matrix is the transpose of the right half of this matrix
        MDS = V_ech[:, m:].transpose()
        return MDS

    def _get_round_constants(self):
        p, Fp, m, capacity, security_level, N = self.p, self.Fp, self.m, self.capacity, self.security_level, self.N
        # generate pseudorandom bytes
        bytes_per_int = ceil(len(bin(p)[2:]) / 8) + 1
        num_bytes = bytes_per_int * 2 * m * (N + 1)
        seed_string = f"rescue({p},{m},{capacity},{security_level})"
        byte_string = SHAKE256(bytes(seed_string, "ascii"), num_bytes)
        # process byte string in chunks
        round_constants = []
        for i in range(2*m*N):
            chunk = byte_string[bytes_per_int*i : bytes_per_int*(i+1)]
            integer = sum(256^j * ZZ(chunk[j]) for j in range(len(chunk)))
            round_constants += [Fp(integer)]
        return round_constants

    def rescue_permutation(self, state, starting_round=0, num_rounds=0):
        Fp, m, alpha, alphainv, N = self.Fp, self.m, self.alpha, self.alphainv, self.N
        MDS, round_constants = self.MDS, self.round_constants
        state = copy(state) # don't accidentally change inplace
        # add first round constants
        if num_rounds:
            N = starting_round + num_rounds
        for i in range(starting_round, N):
            # F
            for j in range(m):
                state[j,0] = state[j,0]^alpha
            state = MDS * state
            for j in range(m):
                state[j,0] += round_constants[2*i*m+j]
            # B
            for j in range(m):
                state[j,0] = state[j,0]^alphainv
            state = MDS * state
            for j in range(m):
                state[j,0] += round_constants[2*i*m+m+j]

        return state

    def rescue_wrapper(self, input_sequence):
        Fp, rate, capacity = self.Fp, self.rate, self.capacity
        padded_input = input_sequence + [Fp(1)]
        while len(padded_input) % rate != 0:
            padded_input.append(Fp(0))
        return self.rescue_hash(padded_input)

    def rescue_hash(self, input_sequence):
        Fp, m, rate, capacity = self.Fp, self.m, self.rate, self.capacity
        assert len(input_sequence) % rate == 0
        # initialize state to all zeros
        state = matrix([[Fp(0)]]*m)
        # absorbing
        absorb_index = 0
        while absorb_index < len(input_sequence):
            for i in range(rate):
                state[i,0] += input_sequence[absorb_index]
                absorb_index += 1
            state = self.rescue_permutation(state)
        # squeezing
        output_sequence = []
        for i in range(rate):
            output_sequence.append(state[i,0])
        return output_sequence

    def rescue_sponge(self, input_sequence, output_length):
        Fp, m, rate, capacity = self.Fp, self.m, self.rate, self.capacity
        assert len(input_sequence) % rate == 0
        # initialize state to all zeros
        state = matrix([[Fp(0)]]*m)
        # absorbing
        absorb_index = 0
        while absorb_index < len(input_sequence):
            for i in range(rate):
                state[i,0] += input_sequence[absorb_index]
                absorb_index += 1
            state = self.rescue_permutation(state)
        # squeezing
        output_sequence = []
        squeeze_index = 0
        while squeeze_index < output_length:
            for i in range(rate):
                output_sequence.append(state[i,0])
                squeeze_index += 1
            if squeeze_index < output_length:
                state = self.rescue_permutation(state)
        return output_sequence[:output_length]

class TestRescue:
    def __init__(self):
        if get_verbose() >= 1: print(f"Testing Rescue Prime (rescue version)…")
        p = previous_prime(2^32) # 2^129
        m = 8
        capacity = 4
        security_level = 128
        assert test_rescue_last_squeeze_poly_system()
        if get_verbose() >= 1: print(f"Testing of Rescue Prime completed")

def rescue_last_squeeze_poly_system(rp, xs, hash_digest):
    m, rate, cap, alpha, alphainv, N, MDS, round_constants = rp.m, rp.rate, rp.capacity, rp.alpha, rp.alphainv, rp.N, rp.MDS, rp.round_constants
    assert len(xs) >= 2*m*(N), f"Too few variables ({len(xs)}) for {N} rounds (state size {m}). Need at least {m*N}."
    assert len(hash_digest) == rate, f"The hash digest needs to be of length {rate} (is {len(hash_digest)})."
    MDS_inv = MDS.inverse()
    system = []
    # variables
    initial_state = matrix(list(xs[:rate]) + [0]*cap).transpose()
    intermediates = matrix([[xs[k*m+rate+j] for k in range(2*N-1)] for j in range(m)])
    final_state = matrix(hash_digest + list(xs[2*N*m-cap:2*N*m])).transpose()
    #first round F
    #new vars = r + m, eq = m
    EQ1 = matrix([el[0]^alpha for el in initial_state.rows()]).transpose()
    cur_vars = intermediates.matrix_from_rows_and_columns([0..(m-1)], [0])
    EQ2 = MDS_inv * (cur_vars - matrix(round_constants[0:m]).transpose())
    system += [n[0] - c[0] for n, c in zip(EQ1.rows(), EQ2.rows())]
    #first round B
    #new vars = m, eq = m
    if N > 1:
        next_vars = intermediates.matrix_from_rows_and_columns([0..(m-1)], [1])
        EQ1 = MDS_inv * (next_vars - matrix(round_constants[m:2*m]).transpose())
        system += [n[0]^alpha - c[0] for n, c in zip(EQ1.rows(), cur_vars.rows())]
    else:
        EQ1 = matrix([el[0] for el in cur_vars.rows()]).transpose()
        EQ2 = MDS_inv * (final_state - matrix(round_constants[m:2*m]).transpose())
        for j in range(m):
            system += [EQ2[j][0]^alpha - EQ1[j][0]]
        # print(system)
    #N intermediate rounds (N-1)*(rescue)
    for i in range(1,N):
        #F
        cur_vars = intermediates.matrix_from_rows_and_columns([0..(m-1)], [2*i-1])
        EQ1 = matrix([el[0]^alpha for el in cur_vars.rows()]).transpose()
        cur_vars = intermediates.matrix_from_rows_and_columns([0..(m-1)], [2*i])
        EQ2 = MDS_inv * (cur_vars - matrix(round_constants[2*i*m:2*i*m+m]).transpose())
        system += [n[0] - c[0] for n, c in zip(EQ1.rows(), EQ2.rows())]
        #B
        if i == N - 1:
            EQ1 = matrix([el[0] for el in cur_vars.rows()]).transpose()
            EQ2 = MDS_inv * (final_state - matrix(round_constants[2*N*m-m:2*N*m]).transpose())
            for j in range(m):
                system += [EQ2[j][0]^alpha - EQ1[j][0]]
        else:
            next_vars = intermediates.matrix_from_rows_and_columns([0..(m-1)], [2*i+1])
            EQ1 = MDS_inv * (next_vars - matrix(round_constants[2*i*m+m:2*i*m+2*m]).transpose())
            system += [n[0]^alpha - c[0] for n, c in zip(EQ1.rows(), cur_vars.rows())]
    # print(system)
    return system

def rescue_last_squeeze_trace(rp, preimage):
    m, rate, cap, alpha, alphainv, N, MDS, round_constants = rp.m, rp.rate, rp.capacity, rp.alpha, rp.alphainv, rp.N, rp.MDS, rp.round_constants
    assert len(preimage) == rate, f"The hash preimage needs to be of length {rate} (is {len(preimage)})."
    MDS_inv = MDS.inverse()
    trace = copy(preimage)
    state = matrix(preimage + [0]*cap).transpose()
    for r in range(N):
        # forward half-round
        state = matrix([el[0]^alpha for el in state.rows()]).transpose()
        state = MDS * state + matrix(round_constants[(2*r+0)*m:(2*r+1)*m]).transpose()
        # second half-round, also forward
        trace.extend(el[0] for el in state.rows())
        state = matrix([el[0]^alphainv for el in state.rows()]).transpose()
        state = MDS * state + matrix(round_constants[(2*r+1)*m:(2*r+2)*m]).transpose()
        if r < N - 1: # not last round
            trace.extend(el[0] for el in state.rows())
        else:
            trace.extend(el[0] for el in state.rows()[rate:m])
    return trace

def test_rescue_last_squeeze_poly_system():
    for p, m, cap, N in [(65519, 2, 1, 2), (101, 7, 4, 2), (1021, 8, 6, 4), (9973, 9, 2, 5)]:
        input_sequence = list(range(m-cap))
        rp = Rescue(p, m, cap, 128, N=N)
        ring = PolynomialRing(GF(p), 'z', 2*m*N)
        hash_digest = rp.rescue_hash(input_sequence)
        system = rescue_last_squeeze_poly_system(rp, ring.gens(), hash_digest)
        trace = rescue_last_squeeze_trace(rp, input_sequence)
        for p in system:
            assert p(trace) == 0, f"Polynomial evaluated at trace does not equal zero!"
            print("ok.")
    return True
