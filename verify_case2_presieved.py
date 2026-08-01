import bisect
import math


# Fixed constants from the proof
N0 = 117465180365547648498934439
R = 16.5
Z0 = N0 ** (1.0 / R)
Z1 = 10**8

K = 1.146
SMALL_K = 2.0 + math.log(K)
S = 14.8
DELTAS = [0.20, 0.60, 0.75, 0.85, 0.93]

PRE_SIEVED_PRIMES = [3]

# Used only when selecting interval endpoints.
#
# The mathematical requirement is S_lower > 0, equivalently
# log(main_term / error_term) > 0.  For numerical robustness, we choose
# interval endpoints only when the stronger inequality
# log(main_term / error_term) > 0.10 holds.  This avoids accepting intervals
# whose positivity depends on subtracting two nearly equal floating-point
# quantities.  This safety margin is not an additional hypothesis in the proof.
INTERVAL_SELECTION_LOG_RATIO = 0.10


def primes_less_than(limit):
    """Return a list of all primes p < limit using a basic sieve."""
    if limit <= 2:
        return []

    is_prime = bytearray([1]) * limit
    is_prime[0] = is_prime[1] = 0

    for d in range(2, int(limit ** 0.5) + 1):
        if is_prime[d]:
            is_prime[d * d : limit : d] = bytearray(
                len(is_prime[d * d : limit : d])
            )

    return [n for n in range(2, limit) if is_prime[n]]


def sieve_factor(s):
    """Return the Friedlander--Iwaniec main-term factor."""
    return 1.0 - (s + 3.0) / (2.0 * math.exp(SMALL_K)) * (
        (2.0 * math.e * SMALL_K) / (s - 3.0)
    ) ** ((s - 3.0) / 2.0)


def endpoint_step(p):
    """
    Return the index spacing between candidate prime endpoints.

    A finer endpoint grid gives the interval search more opportunities to
    stop just before the lower-bound margin fails, reducing the risk that a
    valid covering is missed because the candidate endpoints are too sparse.
    It also requires more product values to be stored and more candidate
    intervals to be tested.  The cumulative products themselves still
    incorporate every prime below each endpoint.

    We therefore use every prime near the bottom of the range and
    increasingly sparse candidate endpoints as z grows.
    """
    if p < 10_000:
        return 1
    if p < 100_000:
        return 10
    if p < 1_000_000:
        return 100
    if p < 10_000_000:
        return 1_000
    return 10_000


def make_candidate_endpoints(primes):
    """Return a simple list of possible interval endpoints."""
    endpoints = [Z0]
    index = bisect.bisect_right(primes, Z0)

    while index < len(primes):
        p = primes[index]
        endpoints.append(float(p))
        index += endpoint_step(p)

    endpoints.append(float(Z1))
    return endpoints


def product_tables(primes, endpoints):
    """
    At each endpoint v, compute logarithms of

        1/2 product_{5 <= p < v} (1 - 2/p),

    and the error term

        product_{p < v, p != 3} (1 + 8/p^delta).

    Logarithms are used to avoid overflow.
    """
    log_W_values = []
    log_error_products = []

    # Account for the factor at p = 2.
    log_W = -math.log(2.0) 
    log_products = [0.0 for _ in DELTAS]
    prime_index = 0

    for v in endpoints:
        while prime_index < len(primes) and primes[prime_index] < v:
            p = primes[prime_index]

            if p >= 5:
                log_W += math.log1p(-2.0 / p)

            if p not in PRE_SIEVED_PRIMES:
                for j, delta in enumerate(DELTAS):
                    log_products[j] += math.log1p(8.0 / p**delta)

            prime_index += 1

        log_W_values.append(log_W)
        log_error_products.append(log_products.copy())

    return log_W_values, log_error_products


def lower_bound(left_index, right_index, endpoints,
                log_W_values, log_error_products):
    """
    Return the best lower bound for the interval

        endpoints[left_index] < z <= endpoints[right_index].
    """
    u = endpoints[left_index]
    v = endpoints[right_index]

    # On the first interval use N0 exactly.
    if left_index == 0:
        X_lower = (N0 - 1) / 3.0
    else:
        X_lower = (u**R - 1.0) / 3.0

    main_term = (
        X_lower
        * math.exp(log_W_values[right_index])
        * sieve_factor(S)
    )
    log_main = math.log(main_term)

    best_delta = None
    best_log_error = None
    best_log_ratio = -math.inf

    # Since the main term is independent of delta, maximising the
    # log-ratio is equivalent to minimising the error term and hence
    # maximising S_lower.
    for j, delta in enumerate(DELTAS):
        log_error = (
            math.log(19.0 / 3.0)
            + S * delta * math.log(v)
            + log_error_products[right_index][j]
        )
        log_ratio = log_main - log_error

        if log_ratio > best_log_ratio:
            best_delta = delta
            best_log_error = log_error
            best_log_ratio = log_ratio

    error_term = math.exp(best_log_error)
    S_lower = main_term - error_term

    return best_delta, S_lower, best_log_ratio


def endpoint_text(x):
    """Print integer endpoints without a trailing .0."""
    if x.is_integer():
        return str(int(x))
    return f"{x:.12f}".rstrip("0").rstrip(".")


def verify_case2():
    factor = sieve_factor(S)

    if S < 2.0 * SMALL_K + 3.0:
        raise RuntimeError("The condition s >= 2k+3 is not satisfied.")
    if factor <= 0.0:
        raise RuntimeError("The main-term sieve factor is not positive.")

    print("Generating primes...")
    primes = primes_less_than(Z1)
    print(f"Generated {len(primes):,} primes below {Z1:,}.")
    print()

    # endpoints = [Z0, p_1, ..., p_m, Z1],
    # where Z0 < p_1 < ... < p_m < Z1.
    # The p_i are selected prime endpoints and need not be consecutive;
    # see endpoint_step(p).
    endpoints = make_candidate_endpoints(primes)

    # For each endpoints[i]:
    #   log_W_values[i] is log W(endpoints[i]);
    #   log_error_products[i][j] is the logarithm of the error product
    #   at endpoints[i] for DELTAS[j].
    log_W_values, log_error_products = product_tables(primes, endpoints)

    interval_count = 0

    # For each interval, lower_bound() maximises over DELTAS.
    # These variables track the minimum optimised results
    # across all accepted intervals.
    smallest_S_lower = math.inf
    smallest_log_ratio = math.inf

    left_index = 0
    final_index = len(endpoints) - 1

    while left_index < final_index:
        last_success = None

        # For a fixed left endpoint, the best log-ratio is nonincreasing
        # as the right endpoint increases: the main term decreases, while
        # every candidate error term increases. Hence, after the first
        # failure, no later candidate endpoint can succeed.
        for right_index in range(left_index + 1, final_index + 1):
            delta, S_lower, log_ratio = lower_bound(
                left_index,
                right_index,
                endpoints,
                log_W_values,
                log_error_products,
            )

            if log_ratio > INTERVAL_SELECTION_LOG_RATIO:
                last_success = (
                    right_index,
                    delta,
                    S_lower,
                    log_ratio,
                )
            else:
                break

        if last_success is None:
            u = endpoints[left_index]
            v = endpoints[left_index + 1]
            raise RuntimeError(
                f"Verification failed immediately after "
                f"({endpoint_text(u)}, {endpoint_text(v)}]."
            )

        right_index, delta, S_lower, log_ratio = last_success
        u = endpoints[left_index]
        v = endpoints[right_index]

        interval_count += 1
        smallest_S_lower = min(smallest_S_lower, S_lower)
        smallest_log_ratio = min(smallest_log_ratio, log_ratio)

        print(
            f"({endpoint_text(u)}, {endpoint_text(v)}]\n"
            f"s={S:.2f}  delta={delta:.2f}  "
            f"S_lower={S_lower:.12e}  Positive={S_lower > 0}"
        )

        left_index = right_index

    print()
    print(
        f"Verified {interval_count:,} intervals covering "
        f"(z_0, {endpoint_text(endpoints[-1])}]."
    )
    print(f"Minimum accepted log-ratio: {smallest_log_ratio:.12f}")
    print(f"Minimum accepted lower bound: {smallest_S_lower:.12e}")

if __name__ == "__main__":
    verify_case2()