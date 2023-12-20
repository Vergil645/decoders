#include <cassert>
#include <iostream>
#include <random>
#include <sstream>
#include <unordered_set>
#include <vector>

#define u64(x) ((std::uint64_t) (x))
#define p_deg(p) (((p) == 0) ? (std::uint64_t) 1 : (std::uint64_t) 63 - __builtin_clzll((p)))
#define p_at(p, d) ((((p) & ((std::uint64_t) 1 << (d))) == 0) ? 0 : 1)

struct polynom {
    polynom() : coef({0}) {}

    explicit polynom(std::uint64_t p) : coef() {
        for (std::uint64_t i = 0; i <= 63 && (u64(1) << i) <= p; ++i)
            coef.push_back(((p & (u64(1) << i)) == 0) ? 0 : 1);
        if (coef.size() == 0) coef.push_back(0);
    }

    explicit polynom(std::vector<std::uint8_t> coef): coef(coef) {
        fix_deg();
    }

    inline std::uint64_t deg() const { return coef.size() - 1; }

    inline std::uint8_t operator[](std::size_t i) const {
        assert(i <= deg());
        return coef[i];
    }

    polynom &operator*=(polynom const &rhs) {
        auto coef_old = coef;
        coef.clear();
        coef.resize(coef_old.size() + rhs.deg());
        for (std::size_t j = 0; j <= rhs.deg(); ++j) {
            if (rhs.coef[j] == 0) continue;
            for (std::size_t i = 0; i < coef_old.size(); ++i)
                coef[i + j] ^= coef_old[i];
        }
        return *this;
    }

    friend bool operator==(polynom const &a, polynom const &b);

    std::vector<std::uint8_t> to_coef() const { return coef; }

    std::string to_string() const {
        std::stringstream res_ss;
        res_ss << (int) coef[0];
        for (std::uint64_t d = 1; d <= deg(); ++d)
            res_ss << ((coef[d] == 0) ? " 0" : " 1");
        return res_ss.str();
    }

    struct HashFunction {
        std::size_t operator()(const polynom& poly) const {
            auto hash_f = std::hash<std::uint8_t>();
            std::size_t res = 0;
            for (std::size_t i = 0; i < poly.coef.size(); ++i)
                res ^= hash_f(poly.coef[i]) << i;
            return res;
        }
    };

private:
    std::vector<std::uint8_t> coef;

    void fix_deg() {
        while (coef.size() > 1 && coef.back() == 0)
            coef.pop_back();
    }
};

const polynom polynom_one(1);

bool operator==(polynom const &a, polynom const &b) { return a.coef == b.coef; }

polynom operator*(polynom a, polynom const &b) { return a *= b; }

struct GF {
    using element_t = std::uint64_t;
    using deg_t = std::uint64_t;

    const deg_t size;

    explicit GF(std::uint64_t const &primitive_polynom) : size(u64(1) << p_deg(primitive_polynom)),
                                                          primitive_polynom(primitive_polynom) {
        element_t primitive_element = 2;

        primitive_deg_to_element.resize(size);
        element_to_primitive_deg.resize(size);
        inv_table.resize(size);

        element_t cur_elem = 1;
        for (deg_t d = 0; d < size; ++d) {
            primitive_deg_to_element[d] = cur_elem;
            element_to_primitive_deg[cur_elem] = d;

            cur_elem = mul_no_cache(cur_elem, primitive_element);
            while (p_deg(cur_elem) >= p_deg(primitive_polynom))
                cur_elem ^= primitive_polynom;
        }

        cur_elem = 1;
        for (deg_t d = 0; d < size; ++d) {
            inv_table[primitive_deg_to_element[size - 1 - d]] = cur_elem;

            cur_elem = mul_no_cache(cur_elem, primitive_element);
            while (p_deg(cur_elem) >= p_deg(primitive_polynom))
                cur_elem ^= primitive_polynom;
        }
    }

    inline element_t primitive_pow(deg_t deg) const { return primitive_deg_to_element[deg]; }

    inline void add_inplace_no_cache(element_t &a, element_t const &b) const { a ^= b; }

    element_t mul_no_cache(element_t a, element_t const &b) const {
        element_t old_a = a;
        a = 0;
        for (deg_t d = 0; d <= p_deg(b); ++d) {
            if ((b & (u64(1) << d)) == 0) continue;
            a ^= old_a << d;
        }
        return a;
    }

    inline element_t mul_cached(element_t const &a, element_t const &b) const {
        return (a == 0 || b == 0) ? 0 : primitive_deg_to_element[
            (element_to_primitive_deg[a] + element_to_primitive_deg[b]) % (size - 1)
        ];
    }

    inline element_t inv_cached(element_t const &a) const {
        return inv_table[a];
    }

    element_t substitute_primitive_pow_cached(polynom const& poly, deg_t deg) const {
        element_t res = 0;
        for (deg_t d = 0; d <= poly.deg(); ++d) {
            if (poly[d] == 0) continue;
            add_inplace_no_cache(res, primitive_deg_to_element[(d * deg) % (size - 1)]);
        }
        return res;
    }

    polynom min_polynom(element_t const& e) const {
        deg_t m = 1;
        deg_t e_deg = element_to_primitive_deg[e];
        while ((e_deg << m) % (size - 1) != e_deg && m < p_deg(primitive_polynom))
            ++m;
        assert((e_deg << m) % (size - 1) == e_deg);

        std::vector<element_t> min_poly_coef = {1};
        for (deg_t i = 0; i < m; ++i) {
            min_poly_coef.insert(min_poly_coef.begin(), 0);
            for (deg_t j = 0; j + 1 < min_poly_coef.size(); ++j) {
                deg_t c1_deg = e_deg << i;
                deg_t c2_deg = element_to_primitive_deg[min_poly_coef[j + 1]];
                add_inplace_no_cache(min_poly_coef[j], primitive_deg_to_element[(c1_deg + c2_deg) % (size - 1)]);
            }
        }

        element_t res_p = 0;
        for (deg_t d = 0; d <= m; ++d) {
            assert(min_poly_coef[d] == 0 || min_poly_coef[d] == 1);
            if (min_poly_coef[d] == 1)
                res_p ^= u64(1) << d;
        }

        return polynom(res_p);
    }

private:
    std::uint64_t primitive_polynom;
    std::vector<element_t> primitive_deg_to_element;
    std::vector<GF::deg_t> element_to_primitive_deg;
    std::vector<element_t> inv_table;
};

struct BCH {
    GF::deg_t n;
    GF::deg_t k;
    GF::deg_t delta;
    polynom g;

    explicit BCH(GF::deg_t n, GF::deg_t delta, GF::deg_t const &primitive_polynom):
        n(n), delta(delta), gf(primitive_polynom) {
        std::unordered_set<polynom, polynom::HashFunction> min_polynoms;
        for (GF::deg_t d = 1; d < delta - 1; d += 2)
            min_polynoms.insert(gf.min_polynom(gf.primitive_pow(d)));

        g = polynom_one;
        for (polynom min_polynom : min_polynoms)
            g *= min_polynom;
        k = n - g.deg();
    }

    std::string encode(std::vector<std::uint8_t> const &src_coef) const {
        std::vector<std::uint8_t> coef = encode_internal(src_coef);
        return coef_to_str(coef);
    }

    std::string decode(std::vector<std::uint8_t> const &y_coef) const {
        std::vector<std::uint8_t> coef = decode_internal(y_coef);
        return coef_to_str(coef);
    }

    double simulate(double noise_level, int num_of_iterations, int max_errors) {
        std::random_device rd;
        std::mt19937 gen32(rd());
        std::uniform_int_distribution<std::uint8_t> uniform_int_dist(0, 1);
        std::bernoulli_distribution bernoulli_dist(noise_level);

        int it, errors;
        for (it = 0, errors = 0; it < num_of_iterations && errors < max_errors; ++it) {
            std::vector<std::uint8_t> src_coef(k);
            for (GF::deg_t i = 0; i < k; ++i)
                src_coef[i] = uniform_int_dist(gen32);
            std::vector<std::uint8_t> encoded_coef = encode_internal(src_coef);

            std::vector<std::uint8_t> y_coef(n);
            for (GF::deg_t d = 0; d < n; ++d) {
                y_coef[d] = encoded_coef[d];
                if (bernoulli_dist(gen32))
                    y_coef[d] ^= 1;
            }
            std::vector<std::uint8_t> decoded_coef = decode_internal(y_coef);

            if (encoded_coef != decoded_coef)
                ++errors;
        }

        return (double) errors / it;
    }

private:
    GF gf;

    std::vector<std::uint8_t> encode_internal(std::vector<std::uint8_t> const &src_coef) const {
        std::vector<std::uint8_t> r(n, 0);
        for (GF::deg_t i = 0; i < k; ++i)
            r[n - k + i] = src_coef[i];

        for (GF::deg_t i = n - 1; i >= n - k; --i) {
            if (r[i] == 0) continue;
            for (GF::deg_t j = 0; j <= n - k; ++j)
                r[i - j] ^= g[n - k - j];
        }

        for (GF::deg_t i = 0; i < k; ++i)
            r[n - k + i] = src_coef[i];

        return r;
    }

    std::vector<std::uint8_t> decode_internal(std::vector<std::uint8_t> y_coef) const {
        polynom y(y_coef);
        std::vector<GF::element_t> s(delta - 1);
        for (GF::deg_t i = 0; i < delta - 1; ++i)
            s[i] = gf.substitute_primitive_pow_cached(y, 1 + i);

        std::vector<GF::element_t> lambda = {1};
        std::vector<GF::element_t> b = {1};
        GF::deg_t m = 0;
        GF::deg_t l = 0;

        for (GF::deg_t r = 1; r <= delta - 1; ++r) {
            if (r % 2 == 0) continue;

            GF::element_t dr = 0;
            for (GF::deg_t j = 0; j <= l; ++j)
                gf.add_inplace_no_cache(dr, gf.mul_cached(lambda[j], s[r - 1 - j]));

            if (dr == 0) continue;

            std::vector<GF::element_t> t = lambda;
            t.resize(std::max(t.size(), b.size() + r - m), 0);
            for (GF::deg_t i = 0; i < b.size(); ++i) {
                GF::deg_t t_i = i + r - m;
                gf.add_inplace_no_cache(t[t_i], gf.mul_cached(dr, b[i]));
            }
            while (t.size() > 1 && t.back() == 0)
                t.pop_back();

            if (2 * l <= r - 1) {
                GF::element_t dr_inv = gf.inv_cached(dr);
                b = lambda;
                for (GF::deg_t i = 0; i < b.size(); ++i)
                    b[i] = gf.mul_cached(b[i], dr_inv);
                lambda = t;
                l = r - l;
                m = r;
            } else {
                lambda = t;
            }
        }

        for (GF::deg_t j = 0; j < n; ++j) {
            GF::element_t subs_res = 0;

            for (GF::deg_t i = 0; i < lambda.size(); ++i)
                gf.add_inplace_no_cache(subs_res, gf.mul_cached(lambda[i], gf.primitive_pow((i * (n - j)) % n)));

            if (subs_res == 0)
                y_coef[j] ^= 1;
        }

        return y_coef;
    }

    std::string coef_to_str(std::vector<std::uint8_t> coef) const {
        std::stringstream res_ss;
        res_ss << (int) coef[0];
        for (GF::deg_t i = 1; i < n; ++i)
            res_ss << " " << (int) coef[i];
        return res_ss.str();
    }
};

int main(void) {
    std::ios_base::sync_with_stdio(false);
    std::cin.tie(nullptr);
    std::cout.tie(nullptr);

    if (!freopen("input.txt", "r", stdin)) {
        return 1;
    }
    if (!freopen("output.txt", "w", stdout)) {
        return 2;
    }

    int n;
    std::uint64_t p;
    int delta;
    std::cin >> n >> p >> delta;

    BCH bch(n, delta, p);

    std::cout << (int) bch.k << std::endl;
    std::cout << bch.g.to_string() << std::endl;

    std::string command;
    while (std::cin >> command) {
        if (command == "Encode") {
            std::vector<std::uint8_t> src_coef(bch.k);
            int x;
            for (std::uint64_t d = 0; d < bch.k; ++d) {
                std::cin >> x;
                src_coef[d] = x;
            }
            std::cout << bch.encode(src_coef) << std::endl;
        } else if (command == "Decode") {
            std::vector<std::uint8_t> y_coef(bch.n);
            int x;
            for (std::uint64_t d = 0; d < bch.n; ++d) {
                std::cin >> x;
                y_coef[d] = x;
            }
            std::cout << bch.decode(y_coef) << std::endl;
        } else if (command == "Simulate") {
            double noise_level;
            int num_of_iterations;
            int max_errors;
            std::cin >> noise_level >> num_of_iterations >> max_errors;
            std::cout << bch.simulate(noise_level, num_of_iterations, max_errors) << std::endl;
        }
    }

    return 0;
}