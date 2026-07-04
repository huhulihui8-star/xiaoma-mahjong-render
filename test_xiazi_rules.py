import unittest

import cloud_mahjong_server as m


def ctx(hand, wild=33, before=None, melds=None, method="self_draw", tile=None, discarder=None):
    return m.WinContext(
        winner=0,
        win_method=method,
        winning_tile=tile,
        discarder=discarder,
        before_win_hand=before or [],
        after_win_hand=hand,
        melds=melds or [],
        win_types=m.win_types(hand, wild, melds or []),
        wild=wild,
        turn_index=5,
        first_discard_done=True,
        wall_remaining=20,
    )


class XiaziRulesTest(unittest.TestCase):
    def test_next_dragon_wraps_suits_and_honors(self):
        self.assertEqual(m.next_dragon(8), 0)
        self.assertEqual(m.next_dragon(17), 9)
        self.assertEqual(m.next_dragon(26), 18)
        self.assertEqual(m.next_dragon(30), 27)
        self.assertEqual(m.next_dragon(33), 31)

    def test_standard_win_without_dragon(self):
        hand = [0, 0, 0, 1, 2, 3, 4, 5, 6, 6, 7, 8, 10, 10]
        self.assertIn("4面子1对子", m.win_types(hand, 33, []))

    def test_standard_win_with_dragon(self):
        hand = [0, 0, 1, 2, 3, 4, 5, 6, 6, 7, 8, 10, 10, 33]
        self.assertIn("4面子1对子", m.win_types(hand, 33, []))

    def test_special_wins(self):
        self.assertIn("四龙", m.win_types([0, 1, 2, 3, 4, 5, 6, 7, 33, 33, 33, 33, 10, 10], 33, []))
        self.assertIn("十一风", m.win_types([27, 28, 29, 30, 31, 32, 33, 27, 28, 29, 30, 1, 4, 7], 0, []))

    def test_dragon_patterns_take_highest(self):
        hand = [0, 0, 0, 1, 1, 1, 9, 9, 9, 18, 18, 18, 33, 33]
        score = m.score_dragon_patterns(ctx(hand, 33))
        self.assertEqual(score["dragons"], 2)
        self.assertIn("二龙", score["patterns"])

    def test_no_dragon_clean_one_suit_is_100(self):
        hand = [0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6]
        score = m.score_dragon_patterns(ctx(hand, 33, method="discard_win", discarder=1))
        self.assertEqual(score["dragons"], 100)
        self.assertTrue(score["full_payout"])
        self.assertIn("无龙清一色", score["patterns"])

    def test_gang_draw_scores_gang_bao(self):
        hand = [0, 0, 0, 1, 2, 3, 4, 5, 6, 6, 7, 8, 10, 10]
        score = m.score_dragon_patterns(ctx(hand, 33, method="gang_draw", tile=10))
        self.assertEqual(score["dragons"], 10)
        self.assertIn("杠爆", score["patterns"])

    def test_discarded_dragon_cannot_be_claim_hu(self):
        r = m.Room("T")
        r.phase = "playing"
        r.dragon = 0
        r.players[1].hand = [0, 0, 1, 2, 3, 4, 5, 6, 6, 7, 8, 10, 10]
        r.open_claim_window(0, 0)
        self.assertTrue(r.claim is None or "hu" not in r.claim["options"].get(1, {}))

    def test_peng_window_and_pass_lock(self):
        r = m.Room("T")
        r.phase = "playing"
        r.dragon = 33
        r.wall = [1, 2, 3, 4]
        r.players[1].human = True
        r.players[1].hand = [5, 5, 9, 10, 11, 12, 13, 14, 20, 21, 22, 31, 31]
        r.open_claim_window(0, 5)
        self.assertTrue(r.claim["options"][1]["peng"])
        r.pass_claim(1)
        self.assertTrue(r.is_locked(1, "peng", 5))

    def test_direct_gang_scores_from_discarder_only(self):
        r = m.Room("T")
        r.phase = "playing"
        r.dragon = 33
        r.wall = [1, 2, 3, 4]
        r.players[1].hand = [5, 5, 5, 9, 10, 11, 12, 13, 14, 20, 21, 22, 31]
        r.open_claim_window(0, 5)
        r.claim_gang(1)
        self.assertEqual(r.players[1].score, 20)
        self.assertEqual(r.players[0].score, -20)
        self.assertEqual(r.players[2].score, 0)

    def test_self_draw_payment_uses_dragons(self):
        r = m.Room("T")
        r.phase = "playing"
        r.dragon = 33
        r.current = 0
        r.turn_index = 5
        r.first_discard_done = True
        r.wall = list(range(20))
        r.players[0].hand = [0, 0, 0, 1, 2, 3, 9, 10, 11, 18, 19, 33, 33, 20]
        r.finish_win(0, None, ["4面子1对子"], before_hand=[], winning_tile=20, win_method="self_draw")
        self.assertEqual(r.lastWinSummary["dragons"], 2)
        self.assertEqual(r.players[0].score, 6)
        self.assertEqual(r.players[1].score, -2)

    def test_full_payout_discard_win_paid_by_discarder(self):
        r = m.Room("T")
        r.phase = "playing"
        r.dragon = 33
        r.players[0].hand = [0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6]
        r.finish_win(0, 1, ["对对碰"], before_hand=r.players[0].hand[:-1], winning_tile=6, win_method="discard_win")
        self.assertEqual(r.lastWinSummary["dragons"], 100)
        self.assertTrue(r.lastWinSummary["fullPayout"])
        self.assertEqual(r.players[0].score, 300)
        self.assertEqual(r.players[1].score, -300)
        self.assertEqual(r.players[2].score, 0)


if __name__ == "__main__":
    unittest.main()
