# FROST feedback

- Schnorr signature scheme doesn't include a CTX string or public key in the challenge computation
- Key generation phase doesn't specify what is the message being signed. How is i encoded? I went with I2OSP(i, 2), allowing t < 2^16.
- Use of A_s as public commitments directly, even though participants get sent C_s, is somewhat confusing. I'd replace A_s with an indexed value into C_s.
- Use of Y for group public key is somewhat confusing. I'd suggest GY, or something else that doesn't conflict with a non-group public key.
- Use of index j instead of i in DKG is confusing. Suggest unifying around i.
- When signing, how does one "validate the message m"?
- When signing, how does one compute H_(1)(p, m, B)? In particular, how does one encode B?
- \lambda_i seems wrong in the draft -- it should be the i-th Lagrange coefficient, right?
- r_(i) notation in signature aggregator computation is overloaded -- suggest rho_(i) (as per paper).
- Step 4 -- where each participant computes the group commitment -- is subtle. I did this wrong the first time around.
- Verifying FROST signature needs to use H2, with CTX and Y included