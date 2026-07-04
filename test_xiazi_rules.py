import unittest

import cloud_mahjong_server as m


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


if __name__ == "__main__":
    unittest.main()
