#include <cassert>
#include <iostream>
#include <random>
#include <sstream>
#include <vector>

#define u32(x) ((std::uint32_t) (x))
#define p_deg(p) (((p) == 0) ? (std::uint32_t) 1 : (std::uint32_t) 63 - __builtin_clzll((p)))
#define p_at(p, d) ((((p) & ((std::uint32_t) 1 << (d))) == 0) ? 0 : 1)

using deg_t = std::uint32_t;

template <typename C>
struct polynom {
    std::vector<C> coef;

    inline deg_t deg() const { return coef.size() - 1; }
};

struct GF_poly2 {
    using Element = std::uint32_t;

    explicit GF_poly2(Element const &primitive_polynom) : size(u32(1) << p_deg(primitive_polynom)),
                                                          primitive_polynom(primitive_polynom) {
        assert(primitive_polynom != 0);

        Element primitive_element = 2;

        deg_to_e.resize(size);
        e_to_deg.resize(size);

        Element cur_elem = 1;
        for (deg_t d = 0; d < size; ++d) {
            deg_to_e[d] = cur_elem;
            e_to_deg[cur_elem] = d;
            cur_elem = rem_no_cache(mul_no_cache(cur_elem, primitive_element));
        }
    }

    inline Element zero() const { return 0; }
    inline bool is_zero(Element e) const { return e == 0; }

    inline Element one() const { return 1; }

    inline void add_inplace(Element &a, Element b) const { a ^= b; }
    inline void sub_inplace(Element &a, Element b) const { add_inplace(a, b); }
    inline void mul_inplace(Element &a, Element b) const {
        a = (a == 0 || b == 0) ? 0 : deg_to_e[(e_to_deg[a] + e_to_deg[b]) % (size - 1)];
    }

    inline Element sub(Element a, Element b) const { sub_inplace(a, b); return a; }
    inline Element mul(Element a, Element b) const { mul_inplace(a, b); return a; }
    inline Element div(Element a, Element b) const {
        assert(b != 0);
        return (a == 0) ? 0 : deg_to_e[(e_to_deg[a] - e_to_deg[b] + size - 1) % (size - 1)];
    }
    inline Element primitive_pow(deg_t d) const { return deg_to_e[d % (size - 1)]; }

    polynom<Element> poly_x(deg_t d) const {
        polynom<Element> res{std::vector<Element>(d + 1, zero())};
        res.coef[d] = one();
        return res;
    }

    void poly_sub_inplace(polynom<Element> &poly_a, polynom<Element> const &poly_b) const {
        poly_a.coef.resize(std::max(poly_a.coef.size(), poly_b.coef.size()), zero());

        deg_t b_deg = poly_b.deg();
        for (deg_t j = 0; j <= b_deg; ++j)
            sub_inplace(poly_a.coef[j], poly_b.coef[j]);
        poly_fix_deg(poly_a);
    }

    void poly_mul_inplace(polynom<Element> &poly_a, polynom<Element> const &poly_b) const {
        deg_t b_deg = poly_b.deg();
        polynom<Element> old_poly_a = poly_a;
        poly_a.coef.assign(old_poly_a.deg() + b_deg + 1, zero());

        for (deg_t j = 0; j <= b_deg; ++j) {
            if (is_zero(poly_b.coef[j])) continue;
            for (deg_t i = 0; i < old_poly_a.coef.size(); ++i)
                add_inplace(poly_a.coef[i + j], mul(poly_b.coef[j], old_poly_a.coef[i]));
        }
        poly_fix_deg(poly_a);
    }

    void poly_mul_constant_inplace(polynom<Element> &poly, Element c) const {
        deg_t poly_deg = poly.deg();
        for (deg_t i = 0; i <= poly_deg; ++i)
            mul_inplace(poly.coef[i], c);
        poly_fix_deg(poly);
    }

    void poly_rem_quot_inplace(polynom<Element> &poly_a, polynom<Element> const &poly_b, polynom<Element> &poly_quot) const {
        deg_t a_deg = poly_a.deg();
        deg_t b_deg = poly_b.deg();
        assert(!is_zero(poly_b.coef[b_deg]));

        poly_quot.coef.assign(a_deg - b_deg + 1, zero());

        for (deg_t i = a_deg; i >= b_deg; --i) {
            if (is_zero(poly_a.coef[i]))
                if (i == 0) break;
                else continue;
            Element c = div(poly_a.coef[i], poly_b.coef[b_deg]);
            poly_quot.coef[i - b_deg] = c;
            for (deg_t j = 0; j <= b_deg; ++j)
                sub_inplace(poly_a.coef[i - j], mul(c, poly_b.coef[b_deg - j]));
            if (i == 0) break;
        }
        poly_fix_deg(poly_a);
    }

    Element substitute_primitive_pow(std::vector<Element> const& coef, deg_t d) const {
        Element res = zero();
        for (deg_t i = 0; i < coef.size(); ++i) {
            if (is_zero(coef[i])) continue;
            add_inplace(res, primitive_pow(e_to_deg[coef[i]] + d * i));
        }
        return res;
    }

    std::string poly_to_string(polynom<Element> &poly) const {
        deg_t poly_deg = poly.deg();
        std::stringstream res_ss;
        res_ss << to_string(poly.coef[0]);
        for (deg_t d = 1; d <= poly_deg; ++d)
            res_ss << " " << to_string(poly.coef[d]);
        return res_ss.str();
    }

    inline std::string to_string(Element e) const { return std::to_string(e); }

    void poly_fix_deg(polynom<Element> &poly) const {
        while (poly.coef.size() > 1 && is_zero(poly.coef.back()))
            poly.coef.pop_back();
    }

private:
    deg_t size;
    Element primitive_polynom;

    std::vector<Element> deg_to_e;
    std::vector<deg_t> e_to_deg;

    Element mul_no_cache(Element a, Element b) const {
        Element old_a = a;
        a = 0;
        for (deg_t d = 0; d <= p_deg(b); ++d) {
            if ((b & (u32(1) << d)) == 0) continue;
            a ^= old_a << d;
        }
        return a;
    }

    Element rem_no_cache(Element a) const {
        while (p_deg(a) >= p_deg(primitive_polynom)) {
            deg_t deg_diff = p_deg(a) - p_deg(primitive_polynom);
            a ^= primitive_polynom << deg_diff;
        }
        return a;
    }
};

struct ReedSolomon {
    deg_t n;
    deg_t k;
    deg_t delta;
    polynom<GF_poly2::Element> g;

    ReedSolomon(deg_t n, deg_t delta, GF_poly2 const &gf):
        n(n), k(n - delta + 1), delta(delta), gf(gf), g{{gf.one()}} {
        for (deg_t i = 0; i < delta - 1; ++i)
            gf.poly_mul_inplace(g, {{gf.primitive_pow(1 + i), gf.one()}});
    }

    std::string encode(std::vector<GF_poly2::Element> const &src_coef) const {
        std::vector<GF_poly2::Element> coef = encode_internal(src_coef);
        return coef_to_str(coef);
    }

    std::string decode(std::vector<GF_poly2::Element> const &y_coef) const {
        std::vector<GF_poly2::Element> coef = decode_internal(y_coef);
        return coef_to_str(coef);
    }

    double simulate(double noise_level, int num_of_iterations, int max_errors) {
        std::random_device rd;
        std::mt19937 gen32(rd());
        std::uniform_int_distribution<GF_poly2::Element> src_symbol_dist(0, n);
        std::uniform_int_distribution<GF_poly2::Element> err_symbol_dist(1, n);
        std::bernoulli_distribution error_dist(noise_level);

        int it, errors;
        for (it = 0, errors = 0; it < num_of_iterations && errors < max_errors; ++it) {
            std::vector<GF_poly2::Element> src_coef(k);
            for (deg_t i = 0; i < k; ++i)
                src_coef[i] = src_symbol_dist(gen32);

            std::vector<GF_poly2::Element> encoded_coef = encode_internal(src_coef);

            std::vector<GF_poly2::Element> y_coef(n);
            for (deg_t d = 0; d < n; ++d) {
                y_coef[d] = encoded_coef[d];
                if (error_dist(gen32))
                    gf.add_inplace(y_coef[d], err_symbol_dist(gen32));
            }

            std::vector<GF_poly2::Element> decoded_coef = decode_internal(y_coef);

            if (encoded_coef != decoded_coef)
                ++errors;
        }

        return (double) errors / it;
    }

private:
    GF_poly2 gf;

    std::vector<GF_poly2::Element> encode_internal(std::vector<GF_poly2::Element> const &src_coef) const {
        std::vector<GF_poly2::Element> r_coef(n, 0);
        for (deg_t i = 0; i < k; ++i)
            r_coef[n - k + i] = src_coef[i];

        for (deg_t i = n - 1; i >= n - k; --i) {
            if (r_coef[i] == 0) continue;
            GF_poly2::Element c = r_coef[i];
            for (deg_t j = 0; j <= n - k; ++j)
                gf.sub_inplace(r_coef[i - j], gf.mul(c, g.coef[n - k - j]));
        }

        for (deg_t i = 0; i < k; ++i)
            r_coef[n - k + i] = src_coef[i];

        return r_coef;
    }

    std::vector<GF_poly2::Element> decode_internal(std::vector<GF_poly2::Element> y_coef) const {
        std::vector<GF_poly2::Element> s_coef(delta - 1);
        for (deg_t i = 0; i < delta - 1; ++i)
            s_coef[i] = gf.substitute_primitive_pow(y_coef, 1 + i);

        deg_t tau = (delta % 2 == 0) ? (delta - 2) / 2 : (delta - 1) / 2;

        polynom<GF_poly2::Element> gamma{std::move(s_coef)};
        gf.poly_fix_deg(gamma);
        if (gf.is_zero(gamma.coef[gamma.deg()])) return y_coef;

        polynom<GF_poly2::Element> r_i = gf.poly_x(tau << 1);
        polynom<GF_poly2::Element> a_i{{gf.zero()}};
        polynom<GF_poly2::Element> lambda{{gf.one()}};
        polynom<GF_poly2::Element> q;

        while (gamma.deg() >= tau) {
            std::swap(r_i.coef, gamma.coef);
            gf.poly_rem_quot_inplace(gamma, r_i, q);

            gf.poly_mul_inplace(q, lambda);
            std::swap(a_i.coef, lambda.coef);
            gf.poly_sub_inplace(lambda, q);
        }

        if (gf.is_zero(lambda.coef[0])) return y_coef;

        GF_poly2::Element c = gf.div(gf.one(), lambda.coef[0]);
        gf.poly_mul_constant_inplace(gamma, c);
        gf.poly_mul_constant_inplace(lambda, c);

        std::vector<deg_t> locators;
        for (deg_t j = 0; j < n; ++j) {
            GF_poly2::Element subs_res = gf.substitute_primitive_pow(lambda.coef, n - j);
            if (gf.is_zero(subs_res))
                locators.push_back(j);
        }

        for (deg_t i : locators) {
            GF_poly2::Element p = gf.mul(gf.primitive_pow(n - i), gf.substitute_primitive_pow(gamma.coef, n - i));
            GF_poly2::Element q = gf.one();
            for (deg_t j : locators) {
                if (j == i) continue;
                gf.mul_inplace(q, gf.sub(gf.one(), gf.primitive_pow(n + j - i)));
            }
            GF_poly2::Element e = gf.div(p, q);
            gf.sub_inplace(y_coef[i], e);
        }

        return y_coef;
    }

    std::string coef_to_str(std::vector<GF_poly2::Element> coef) const {
        std::stringstream res_ss;
        res_ss << coef[0];
        for (deg_t i = 1; i < n; ++i)
            res_ss << " " << gf.to_string(coef[i]);
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
    std::uint32_t p;
    int delta;
    std::cin >> n >> p >> delta;

    GF_poly2 gf(p);
    ReedSolomon reed_solomon(n, delta, gf);

    std::cout << reed_solomon.k << std::endl;
    std::cout << gf.poly_to_string(reed_solomon.g) << std::endl;

    std::string command;
    while (std::cin >> command) {
        if (command == "Encode") {
            std::vector<GF_poly2::Element> src_coef(reed_solomon.k);
            for (deg_t d = 0; d < reed_solomon.k; ++d)
                std::cin >> src_coef[d];
            std::cout << reed_solomon.encode(src_coef) << std::endl;
        } else if (command == "Decode") {
            std::vector<GF_poly2::Element> y_coef(reed_solomon.n);
            for (std::uint32_t d = 0; d < reed_solomon.n; ++d)
                std::cin >> y_coef[d];
            std::cout << reed_solomon.decode(y_coef) << std::endl;
        } else if (command == "Simulate") {
            double noise_level;
            int num_of_iterations;
            int max_errors;
            std::cin >> noise_level >> num_of_iterations >> max_errors;
            std::cout << reed_solomon.simulate(noise_level, num_of_iterations, max_errors) << std::endl;
        }
    }

    return 0;
}