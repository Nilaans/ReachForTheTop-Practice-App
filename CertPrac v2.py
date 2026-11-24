import csv
import json
import os
import queue
import random
import re
import sys
import threading
import time
from difflib import SequenceMatcher
import tkinter as tk
from tkinter import filedialog

import pygame

# Optional: Google Gemini for answer checking and question categories
try:
    import google.generativeai as genai
    GEMINI_AVAILABLE = True
except ImportError:
    GEMINI_AVAILABLE = False

# The old gemini-1.5 models have been shut down; override with GEMINI_MODEL if needed.
GEMINI_MODEL = os.getenv("GEMINI_MODEL", "gemini-3.8-flash")
EXIT_PASSWORD = "password123"

# ---- Roman palette (flat colours only) ----
PARCHMENT = (237, 228, 206)
MARBLE = (247, 242, 229)
SAND = (226, 214, 184)
INK = (48, 38, 32)
PURPLE = (94, 28, 76)
PURPLE_HOVER = (120, 44, 98)
GOLD = (191, 150, 42)
BRONZE = (142, 98, 20)
CRIMSON = (150, 32, 32)
LAUREL = (66, 102, 54)
LAUREL_HOVER = (82, 122, 68)
STONE = (140, 128, 110)

SERIF_FONTS = ("trajanpro,cinzel,palatinolinotype,bookantiqua,georgia,"
               "garamond,timesnewroman,dejavuserif")


def to_roman(n):
    if not 0 < n < 4000:
        return str(n)
    out = ""
    for value, sym in ((1000, "M"), (900, "CM"), (500, "D"), (400, "CD"),
                       (100, "C"), (90, "XC"), (50, "L"), (40, "XL"),
                       (10, "X"), (9, "IX"), (5, "V"), (4, "IV"), (1, "I")):
        while n >= value:
            out += sym
            n -= value
    return out


class QuizBuzzer:
    WIDTH, HEIGHT = 1000, 720
    QUESTION_PANEL = pygame.Rect(50, 150, 900, 230)
    QUESTION_TEXT = pygame.Rect(78, 172, 844, 186)

    def __init__(self):
        # Data
        self.csv_file = None
        self.questions = []
        self.available_questions = []
        self.question_column = 1
        self.selected_column = 1
        self.preview_row = ("", "")
        self.load_error = ""
        self.file_error = ""
        self.file_input_text = ""
        self.question_count_text = ""
        self.question_count_error = ""
        self.question_categories = []
        self.category_wrong_counts = {}
        self.category_cache = {}
        self.category_names = {}

        # Settings
        self.allow_retry = True
        self.buzz_window_seconds = 5.0
        self.screen_state = "file_input"

        self.reset_run_state()

        # Pygame
        pygame.init()
        self.width, self.height = self.WIDTH, self.HEIGHT
        self.screen = pygame.display.set_mode((self.width, self.height))
        pygame.display.set_caption("Quiz Buzzer - Forum Edition")
        self.clock = pygame.time.Clock()

        # Fonts
        self._font_cache = {}
        self.title_font = self.font(46, True)
        self.heading_font = self.font(30, True)
        self.button_font = self.font(26, True)
        self.question_font = self.font(34)
        self.text_font = self.font(26)
        self.small_font = self.font(21)
        self.current_question_font = None

        self.background = self.build_background()

        # Audio
        self.buzzer_sound = None
        try:
            pygame.mixer.init()
            self.audio_enabled = True
            self.create_buzzer_sound()
        except Exception as e:
            print(f"Could not initialize audio: {e}")
            self.audio_enabled = False

        # Gemini
        self.use_ai = False
        self.model = None
        api_key = os.getenv("GEMINI_API_KEY")
        if GEMINI_AVAILABLE and api_key:
            try:
                genai.configure(api_key=api_key)
                self.model = genai.GenerativeModel(GEMINI_MODEL)
                self.use_ai = True
                print(f"Using Gemini ({GEMINI_MODEL}) for answer checking.")
            except Exception as e:
                print(f"Could not initialize Gemini: {e}")

    # ------------------------------------------------------------------ state
    def reset_run_state(self):
        self.score = 0
        self.answered = 0
        self.current_question_num = 0
        self.total_questions = len(self.questions)
        self.second_try_correct_count = 0
        self.wrong_count = 0
        self.buzz_times = []
        self.buzzed = False
        self.question_start_time = 0.0
        self.current_display_text = ""
        self.status_message = ""
        self.status_color = INK
        self.timer_fraction = None
        self.input_text = ""
        self.input_label = ""
        self.awaiting_input = False
        self.show_instructions = True
        self.report = []

    def set_status(self, message, color=INK):
        self.status_message = message
        self.status_color = color

    def quit_app(self):
        pygame.quit()
        sys.exit()

    # ------------------------------------------------------------------ fonts / drawing helpers
    def font(self, size, bold=False):
        key = (size, bold)
        if key not in self._font_cache:
            self._font_cache[key] = pygame.font.SysFont(SERIF_FONTS, size, bold=bold)
        return self._font_cache[key]

    def build_meander(self, width, color, c=4, thickness=2):
        """Greek-key strip drawn from lines (no images)."""
        height = 5 * c + thickness
        surf = pygame.Surface((width, height), pygame.SRCALPHA)
        pts = [(0, 5), (0, 0), (5, 0), (5, 4), (2, 4), (2, 2), (3, 2)]
        for x in range(0, width, 6 * c):
            pygame.draw.lines(surf, color, False,
                              [(x + px * c, py * c) for px, py in pts], thickness)
        pygame.draw.line(surf, color, (0, 5 * c), (width, 5 * c), thickness)
        return surf

    def build_background(self):
        w, h = self.width, self.height
        bg = pygame.Surface((w, h))
        bg.fill(PARCHMENT)
        pygame.draw.rect(bg, PURPLE, (0, 0, w, 70))
        pygame.draw.rect(bg, GOLD, (0, 70, w, 6))
        title = self.title_font.render("QUIZ BUZZER", True, PARCHMENT)
        rect = title.get_rect(center=(w // 2, 35))
        bg.blit(title, rect)
        for side in (-1, 1):
            cx = w // 2 + side * (rect.width // 2 + 40)
            pygame.draw.polygon(bg, GOLD, [(cx, 25), (cx + 10, 35), (cx, 45), (cx - 10, 35)])
            pygame.draw.line(bg, GOLD, (cx + side * 20, 35), (cx + side * 140, 35), 2)
        meander = self.build_meander(w, PURPLE)
        bg.blit(meander, (0, 84))
        bg.blit(meander, (0, h - 44))
        pygame.draw.rect(bg, GOLD, (0, h - 18, w, 4))
        pygame.draw.rect(bg, PURPLE, (0, h - 14, w, 14))
        return bg

    def draw_background(self):
        self.screen.blit(self.background, (0, 0))

    def wrap_text(self, text, font, max_width):
        lines, current = [], ""
        for word in text.split():
            while font.size(word)[0] > max_width:
                n = len(word)
                while n > 1 and font.size(word[:n])[0] > max_width:
                    n -= 1
                if current:
                    lines.append(current)
                    current = ""
                lines.append(word[:n])
                word = word[n:]
            if not word:
                continue
            trial = f"{current} {word}".strip()
            if font.size(trial)[0] <= max_width:
                current = trial
            else:
                if current:
                    lines.append(current)
                current = word
        if current:
            lines.append(current)
        return lines or [""]

    def draw_text(self, text, font, color, x, y, align="left", max_width=None, middle=False):
        """Draw (wrapped) text. y is the top, or the vertical centre if middle=True."""
        if max_width is None:
            max_width = self.width - 40
        lines = self.wrap_text(text, font, max_width)
        lh = font.get_linesize()
        total = lh * len(lines)
        top = y - total // 2 if middle else y
        for i, line in enumerate(lines):
            if not line:
                continue
            surf = font.render(line, True, color)
            ly = top + i * lh
            if align == "center":
                rect = surf.get_rect(midtop=(x, ly))
            elif align == "right":
                rect = surf.get_rect(topright=(x, ly))
            else:
                rect = surf.get_rect(topleft=(x, ly))
            self.screen.blit(surf, rect)
        return total

    def draw_centered(self, text, font, color, y, max_width=None):
        return self.draw_text(text, font, color, self.width // 2, y,
                              align="center", middle=True, max_width=max_width)

    @staticmethod
    def ellipsize(text, font, width):
        if font.size(text)[0] <= width:
            return text
        while text and font.size(text + "...")[0] > width:
            text = text[:-1]
        return text + "..."

    @staticmethod
    def fit_tail(text, font, width):
        while text and font.size(text)[0] > width:
            text = text[1:]
        return text

    def fit_font(self, question):
        for size in (40, 36, 32, 28, 26, 24, 22):
            f = self.font(size)
            lines = self.wrap_text(question, f, self.QUESTION_TEXT.width)
            if len(lines) * f.get_linesize() <= self.QUESTION_TEXT.height:
                return f
        return self.font(20)

    def draw_panel(self, rect):
        pygame.draw.rect(self.screen, MARBLE, rect)
        pygame.draw.rect(self.screen, GOLD, rect, 3)
        pygame.draw.rect(self.screen, STONE, rect.inflate(-16, -16), 1)

    def draw_button(self, rect, label, sub=None, selected=False, primary=False):
        hover = rect.collidepoint(pygame.mouse.get_pos())
        if primary:
            fill, fg, inner = (LAUREL_HOVER if hover else LAUREL), PARCHMENT, GOLD
        elif selected:
            fill, fg, inner = (PURPLE_HOVER if hover else PURPLE), PARCHMENT, GOLD
        else:
            fill, fg, inner = (SAND if hover else MARBLE), INK, STONE
        pygame.draw.rect(self.screen, fill, rect)
        pygame.draw.rect(self.screen, GOLD, rect, 3)
        pygame.draw.rect(self.screen, inner, rect.inflate(-14, -14), 1)
        if sub:
            self.draw_text(label, self.heading_font, fg, rect.centerx, rect.centery - 16,
                           align="center", middle=True)
            self.draw_text(self.ellipsize(sub, self.small_font, rect.width - 32),
                           self.small_font, fg, rect.centerx, rect.centery + 20,
                           align="center", middle=True)
        else:
            self.draw_text(label, self.button_font, fg, rect.centerx, rect.centery,
                           align="center", middle=True)

    def draw_input_box(self, rect, text, font, center=False):
        pygame.draw.rect(self.screen, MARBLE, rect)
        pygame.draw.rect(self.screen, GOLD, rect, 3)
        shown = self.fit_tail(text, font, rect.width - 28)
        surf = font.render(shown, True, INK) if shown else None
        w = surf.get_width() if surf else 0
        x = rect.centerx - w // 2 if center else rect.left + 14
        if surf:
            self.screen.blit(surf, surf.get_rect(midleft=(x, rect.centery)))
        if int(time.time() * 2) % 2 == 0:
            cx = x + w + 2
            half = font.get_height() // 2 - 2
            pygame.draw.line(self.screen, INK, (cx, rect.centery - half),
                             (cx, rect.centery + half), 2)

    # ------------------------------------------------------------------ audio
    def create_buzzer_sound(self):
        try:
            import numpy as np
            freq, _fmt, channels = pygame.mixer.get_init()
            n = int(freq * 0.8)
            t = np.arange(n) / freq
            half = n // 2
            wave = np.concatenate([np.sin(2 * np.pi * 800 * t[:half]),
                                   np.sin(2 * np.pi * 400 * t[half:])])
            wave = wave * np.linspace(1.0, 0.3, n)
            wave = (wave / np.max(np.abs(wave)) * 0.8 * 32767).astype(np.int16)
            if channels > 1:
                wave = np.column_stack([wave] * channels)
            self.buzzer_sound = pygame.sndarray.make_sound(wave)
        except Exception as e:
            print(f"Could not create buzzer sound: {e}")
            self.buzzer_sound = None

    def play_buzzer(self):
        if self.audio_enabled and self.buzzer_sound:
            try:
                self.buzzer_sound.play()
            except Exception:
                pass

    # ------------------------------------------------------------------ files
    def select_csv_file(self):
        root = tk.Tk()
        root.withdraw()
        root.attributes("-topmost", True)
        try:
            return filedialog.askopenfilename(
                title="Select your quiz CSV file",
                filetypes=[("CSV files", "*.csv"), ("All files", "*.*")])
        finally:
            root.destroy()

    @staticmethod
    def get_clipboard_text():
        try:
            import pyperclip
            return pyperclip.paste()
        except Exception:
            pass
        root = None
        try:
            root = tk.Tk()
            root.withdraw()
            return root.clipboard_get()
        except Exception:
            return ""
        finally:
            if root is not None:
                root.destroy()

    @staticmethod
    def read_csv_rows(path):
        last_error = None
        for encoding in ("utf-8-sig", "cp1252"):
            try:
                with open(path, "r", encoding=encoding, newline="") as f:
                    return [row for row in csv.reader(f) if len(row) >= 2]
            except UnicodeDecodeError as e:
                last_error = e
        raise last_error

    def try_set_file(self, path):
        path = os.path.expanduser(path.strip().strip('"').strip("'"))
        if not (os.path.isfile(path) and path.lower().endswith(".csv")):
            return "File not found, or not a .csv file."
        self.csv_file = path
        self.file_input_text = path
        self.load_error = ""
        try:
            rows = self.read_csv_rows(path)
            self.preview_row = (rows[0][0], rows[0][1]) if rows else ("", "")
        except Exception:
            self.preview_row = ("", "")
        self.selected_column = 1
        self.screen_state = "column_selection"
        return ""

    def load_questions(self):
        self.category_cache = {}
        try:
            rows = self.read_csv_rows(self.csv_file)
        except (OSError, UnicodeDecodeError, csv.Error) as e:
            self.load_error = f"Could not read file: {e}"
            return False
        q_i, a_i = (0, 1) if self.question_column == 1 else (1, 0)
        pairs = [(r[q_i].strip(), r[a_i].strip()) for r in rows]
        pairs = [(q, a) for q, a in pairs if q and a]
        if not pairs:
            self.load_error = "No question/answer rows found in that file."
            return False
        self.available_questions = pairs
        self.questions = pairs.copy()
        self.total_questions = len(pairs)
        self.load_error = ""
        print(f"Loaded {len(pairs)} questions")
        return True

    # ------------------------------------------------------------------ AI
    def ask_gemini(self, prompt, max_tokens, json_mode=False):
        config = {"temperature": 0.0, "max_output_tokens": max_tokens}
        if json_mode:
            config["response_mime_type"] = "application/json"
        response = self.model.generate_content(
            prompt,
            generation_config=genai.types.GenerationConfig(**config),
            request_options={"timeout": 30},
        )
        return (response.text or "").strip()

    def request_categories(self, pairs):
        """Return {question: category} for the given (question, answer) pairs."""
        items = [{"q": q, "a": a} for q, a in pairs]
        prompt = (
            "Assign each quiz item a short subject category (1-3 words) based on its key "
            "people, places, events or topics. Reuse the same label for related items, and "
            "prefer a modest number of broad categories over one per item.\n"
            "Reply with only a JSON array of strings, one per item, in the same order.\n\n"
            f"Items:\n{json.dumps(items, ensure_ascii=False)}"
        )
        try:
            text = self.ask_gemini(prompt, 8192, json_mode=True)
            text = text[text.index("["): text.rindex("]") + 1]
            labels = json.loads(text)
            if (not isinstance(labels, list) or len(labels) != len(pairs)
                    or any(not isinstance(c, str) or not c.strip() for c in labels)):
                raise ValueError("invalid category list")
            result = {}
            for (q, _), label in zip(pairs, labels):
                label = label.strip()
                result[q] = self.category_names.setdefault(label.casefold(), label)
            return result
        except Exception as e:
            print(f"Could not categorize questions: {e}")
            return {}

    def categorize_questions(self):
        unknown = [(q, a) for q, a in self.questions if q not in self.category_cache]
        if unknown and self.use_ai:
            categories = self.run_ai_request(
                lambda: self.request_categories(unknown),
                "The scribes are sorting your questions...")
            self.category_cache.update(categories)
        return [self.category_cache.get(q, "Uncategorized") for q, _ in self.questions]

    def run_ai_request(self, request, message):
        result_queue = queue.Queue()

        def make_request():
            try:
                result_queue.put((True, request()))
            except Exception as error:
                result_queue.put((False, error))

        threading.Thread(target=make_request, daemon=True).start()
        while True:
            try:
                succeeded, result = result_queue.get_nowait()
            except queue.Empty:
                pass
            else:
                if not succeeded:
                    raise result
                return result

            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    self.quit_app()
            self.draw_background()
            self.draw_centered(message, self.heading_font, INK, 340)
            pygame.display.flip()
            self.clock.tick(30)

    def check_answer_with_ai(self, user_answer, correct_answer, question):
        prompt = (
            "You are a lenient, friendly quiz grader. Decide whether the student's answer "
            "deserves credit. The official answer may be terse or incomplete, so use the "
            "question for context. When in doubt, give credit.\n\n"
            f"Question: {question}\n"
            f"Official answer: {correct_answer}\n"
            f"Student answer: {user_answer}\n\n"
            "Reply with exactly one word:\n"
            "CORRECT - the student identifies the same person, place, thing, idea or number "
            "as the official answer, or gives another reasonable correct answer to the "
            "question. Accept different wording, synonyms, alternate or partial names "
            "(e.g. surname only), abbreviations, translations, misspellings, extra correct "
            "detail, and answers that cover the main point even if a secondary part is "
            "missing.\n"
            "CLOSE - mostly right, but one minor detail is off.\n"
            "WRONG - only if the student names something clearly different, contradicts the "
            "official answer on its key fact, or gives no real answer."
        )
        try:
            response = self.run_ai_request(
                lambda: self.ask_gemini(prompt, 2048), "Checking your answer...")
            text = response.upper().lstrip("*`\"' ")
            if text.startswith("CORRECT"):
                return True, "exact"
            if text.startswith("CLOSE"):
                return True, "close"
            if text.startswith(("WRONG", "INCORRECT")):
                return False, "wrong"
            raise ValueError(f"unexpected reply: {text!r}")
        except Exception as e:
            print(f"AI grading failed, using fuzzy match: {e}")
            return self.check_answer_fuzzy(user_answer, correct_answer)

    @staticmethod
    def normalize(text):
        text = re.sub(r"[^\w\s]", "", text.lower())
        text = re.sub(r"\b(the|a|an)\b", " ", text)
        return " ".join(text.split())

    def check_answer_fuzzy(self, user_answer, correct_answer):
        user = self.normalize(user_answer)
        correct = self.normalize(correct_answer)
        if not user:
            return False, "wrong"
        if user == correct:
            return True, "exact"
        if set(correct.split()) <= set(user.split()):
            return True, "close"
        ratio = SequenceMatcher(None, user, correct).ratio()
        if ratio >= 0.75:
            return True, "close"
        if (user in correct or correct in user) and ratio >= 0.6:
            return True, "close"
        return False, "wrong"

    def check_answer(self, user_answer, correct_answer, question=""):
        if not user_answer.strip():
            return False, "wrong"
        if self.use_ai:
            return self.check_answer_with_ai(user_answer, correct_answer, question)
        return self.check_answer_fuzzy(user_answer, correct_answer)

    # ------------------------------------------------------------------ setup screens
    def draw_file_input_screen(self):
        self.draw_background()
        self.draw_centered("Enter or paste the path to your CSV file", self.heading_font, INK, 150)
        box = pygame.Rect(100, 200, self.width - 200, 56)
        self.draw_input_box(box, self.file_input_text, self.small_font)

        browse = pygame.Rect(self.width // 2 - 110, 290, 220, 54)
        self.draw_button(browse, "BROWSE FILES", primary=True)
        submit = None
        if self.file_input_text.strip():
            submit = pygame.Rect(self.width // 2 - 110, 360, 220, 54)
            self.draw_button(submit, "CONTINUE", selected=True)

        self.draw_centered("Type or paste a path, drag a CSV onto this window, or browse.",
                           self.small_font, STONE, 450)
        if self.file_error:
            self.draw_centered(self.file_error, self.small_font, CRIMSON, 490)
        ai_note = (f"Answer checking: Gemini ({GEMINI_MODEL})" if self.use_ai
                   else "Answer checking: fuzzy matching (set GEMINI_API_KEY for AI grading)")
        self.draw_centered(ai_note, self.small_font, BRONZE, 600)
        self.draw_centered("Press ESC to exit", self.small_font, STONE, 640)
        return browse, submit

    def draw_column_selection_screen(self):
        self.draw_background()
        if self.csv_file:
            self.draw_centered(f"File: {os.path.basename(self.csv_file)}",
                               self.small_font, BRONZE, 132)
        self.draw_centered("Which column contains the QUESTIONS?", self.heading_font, INK, 180)
        r1 = pygame.Rect(self.width // 2 - 320, 225, 300, 130)
        r2 = pygame.Rect(self.width // 2 + 20, 225, 300, 130)
        self.draw_button(r1, "COLUMN I", sub=self.preview_row[0] or None,
                         selected=self.selected_column == 1)
        self.draw_button(r2, "COLUMN II", sub=self.preview_row[1] or None,
                         selected=self.selected_column == 2)
        cont = pygame.Rect(self.width // 2 - 150, 395, 300, 60)
        self.draw_button(cont, "CONTINUE", primary=True)
        if self.load_error:
            self.draw_centered(self.load_error, self.small_font, CRIMSON, 490)
        self.draw_centered("Press 1 or 2 to choose, ENTER to continue", self.small_font, BRONZE, 560)
        self.draw_centered("Press ESC to go back", self.small_font, STONE, 640)
        return r1, r2, cont

    def draw_question_count_selection_screen(self):
        self.draw_background()
        n = len(self.available_questions)
        self.draw_centered("How many questions?", self.heading_font, INK, 175)
        self.draw_centered(f"Choose 1 to {n}, or leave blank to use all {n}.",
                           self.small_font, BRONZE, 220)
        box = pygame.Rect(self.width // 2 - 150, 265, 300, 64)
        self.draw_input_box(box, self.question_count_text, self.title_font, center=True)
        cont = pygame.Rect(self.width // 2 - 150, 360, 300, 60)
        self.draw_button(cont, "CONTINUE", primary=True)
        if self.question_count_error:
            self.draw_centered(self.question_count_error, self.small_font, CRIMSON, 460)
        self.draw_centered("Press ENTER to continue, or ESC to go back", self.small_font, STONE, 640)
        return cont

    def draw_retry_selection_screen(self):
        self.draw_background()
        if self.csv_file:
            self.draw_centered(f"File: {os.path.basename(self.csv_file)}",
                               self.small_font, BRONZE, 132)
        self.draw_centered("Allow a second chance on wrong answers?", self.heading_font, INK, 180)
        yes = pygame.Rect(self.width // 2 - 320, 225, 300, 130)
        no = pygame.Rect(self.width // 2 + 20, 225, 300, 130)
        self.draw_button(yes, "YES", sub="Second chance", selected=self.allow_retry)
        self.draw_button(no, "NO", sub="Single attempt", selected=not self.allow_retry)
        start = pygame.Rect(self.width // 2 - 150, 395, 300, 60)
        self.draw_button(start, "START QUIZ", primary=True)
        self.draw_centered("Press Y or N to choose, ENTER to start", self.small_font, BRONZE, 560)
        self.draw_centered("Press ESC to go back", self.small_font, STONE, 640)
        return yes, no, start

    def apply_question_count(self):
        n = len(self.available_questions)
        text = self.question_count_text.strip()
        requested = int(text) if text else n
        if not 1 <= requested <= n:
            self.question_count_error = f"Enter a number from 1 to {n}."
            return False
        self.questions = random.sample(self.available_questions, requested)
        self.total_questions = requested
        self.question_categories = self.categorize_questions()
        self.category_wrong_counts = {c: 0 for c in self.question_categories}
        self.question_count_error = ""
        return True

    # ------------------------------------------------------------------ quiz screen
    def draw_screen(self):
        self.draw_background()
        if self.show_instructions:
            self.draw_instructions()
        else:
            self.draw_question_view()
        pygame.display.flip()

    def draw_instructions(self):
        panel = pygame.Rect(100, 120, 800, 430)
        self.draw_panel(panel)
        self.draw_centered("THE RULES", self.heading_font, PURPLE, 160)
        rules = [
            "Each question is revealed word by word.",
            "Press SPACE to buzz in at any time. After the last word you have "
            f"{self.buzz_window_seconds:g} more seconds to buzz.",
            "Type your answer and press ENTER.",
            ("A wrong answer earns a second chance (not scored)." if self.allow_retry
             else "You have a single attempt at each question."),
            f"Type '{EXIT_PASSWORD}' as an answer to leave at any time.",
        ]
        y = 205
        for i, rule in enumerate(rules, 1):
            self.draw_text(to_roman(i) + ".", self.text_font, BRONZE, 140, y)
            h = self.draw_text(rule, self.text_font, INK, 215, y, max_width=640)
            y += h + 18
        self.draw_centered("Press SPACE to begin", self.heading_font, PURPLE, 590)

    def draw_question_view(self):
        self.draw_text(f"Score  {self.score} / {self.answered}", self.text_font, BRONZE, 50, 116)
        if self.total_questions > 0:
            label = (f"Question {to_roman(self.current_question_num)} "
                     f"of {to_roman(self.total_questions)}")
            self.draw_text(label, self.text_font, BRONZE, self.width - 50, 116, align="right")

        self.draw_panel(self.QUESTION_PANEL)
        if self.current_display_text:
            font = self.current_question_font or self.question_font
            self.draw_text(self.current_display_text, font, INK,
                           self.QUESTION_TEXT.x, self.QUESTION_TEXT.y,
                           max_width=self.QUESTION_TEXT.width)

        if self.timer_fraction is not None:
            bar = pygame.Rect(50, 392, 900, 10)
            pygame.draw.rect(self.screen, STONE, bar, 1)
            fill = bar.copy()
            fill.width = int(bar.width * max(0.0, min(1.0, self.timer_fraction)))
            color = CRIMSON if self.timer_fraction < 0.3 else PURPLE
            pygame.draw.rect(self.screen, color, fill)

        if self.status_message:
            self.draw_text(self.status_message, self.text_font, self.status_color,
                           self.width // 2, 438, align="center", middle=True,
                           max_width=self.width - 120)

        if self.awaiting_input:
            self.draw_text(self.input_label, self.text_font, BRONZE, 150, 484)
            self.draw_input_box(pygame.Rect(150, 520, 700, 54), self.input_text, self.text_font)
            self.draw_centered("Press ENTER to submit", self.small_font, STONE, 600)

    # ------------------------------------------------------------------ quiz flow helpers
    def pause(self, ms):
        end = time.perf_counter() + ms / 1000
        while time.perf_counter() < end:
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    self.quit_app()
            self.draw_screen()
            self.clock.tick(60)

    def register_buzz(self):
        self.buzzed = True
        self.buzz_times.append(time.perf_counter() - self.question_start_time)
        self.play_buzzer()
        self.set_status("BUZZED IN!", BRONZE)
        self.draw_screen()
        self.pause(450)

    def poll_for_buzz(self, duration, allow_buzz=True):
        """Wait up to `duration` seconds, reacting to SPACE immediately. True if buzzed."""
        deadline = time.perf_counter() + duration
        while True:
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    self.quit_app()
                if (allow_buzz and event.type == pygame.KEYDOWN
                        and event.key == pygame.K_SPACE and not self.buzzed):
                    self.register_buzz()
                    return True
            if time.perf_counter() >= deadline:
                return False
            self.clock.tick(120)

    def read_question(self, question, full_read=False):
        self.buzzed = False
        self.current_display_text = ""
        if not full_read:
            self.question_start_time = time.perf_counter()
            self.set_status("Press SPACE to buzz in!", LAUREL)
        else:
            self.set_status("Reading the full question (no buzzing)", BRONZE)

        delay = 0.10 if full_read else 0.20
        for word in question.split():
            self.current_display_text += word + " "
            self.draw_screen()
            if self.poll_for_buzz(delay, allow_buzz=not full_read):
                return
        if full_read:
            self.pause(500)

    def wait_for_buzz(self):
        """Allow a few more seconds to buzz after the full question has been shown."""
        if self.buzzed:
            return True
        deadline = time.perf_counter() + self.buzz_window_seconds
        while time.perf_counter() < deadline:
            left = deadline - time.perf_counter()
            self.timer_fraction = left / self.buzz_window_seconds
            self.set_status(f"Buzz now!  {left:.1f}s", BRONZE)
            self.draw_screen()
            if self.poll_for_buzz(1 / 60):
                self.timer_fraction = None
                return True
        self.timer_fraction = None
        return False

    def get_user_input(self, label="Your answer", status="", color=INK):
        self.input_text = ""
        self.input_label = label
        self.awaiting_input = True
        self.set_status(status, color)
        while self.awaiting_input:
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    self.quit_app()
                elif event.type == pygame.KEYDOWN:
                    if event.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
                        self.awaiting_input = False
                    elif event.key == pygame.K_BACKSPACE:
                        self.input_text = self.input_text[:-1]
                    elif event.unicode and event.unicode.isprintable() and len(self.input_text) < 300:
                        self.input_text += event.unicode
            self.draw_screen()
            self.clock.tick(60)
        answer = self.input_text.strip()
        if answer == EXIT_PASSWORD:
            self.quit_app()
        return answer

    def grade(self, answer, correct_answer, question):
        if self.use_ai and answer:
            self.set_status("Checking your answer...", BRONZE)
            self.draw_screen()
        return self.check_answer(answer, correct_answer, question)

    def wait_for_space(self):
        while True:
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    self.quit_app()
                if event.type == pygame.KEYDOWN and event.key == pygame.K_SPACE:
                    return
            self.draw_screen()
            self.clock.tick(60)

    # ------------------------------------------------------------------ quiz loop
    def run_quiz(self):
        self.reset_run_state()
        self.category_wrong_counts = {c: 0 for c in self.question_categories}

        self.draw_screen()
        self.wait_for_space()
        self.show_instructions = False

        for idx, (question, correct_answer) in enumerate(self.questions, 1):
            self.current_question_num = idx
            self.current_display_text = ""
            self.timer_fraction = None
            self.set_status("")
            self.current_question_font = self.fit_font(question)
            self.draw_screen()
            self.pause(500)

            self.read_question(question)
            did_buzz = self.wait_for_buzz()

            answer, answer2, outcome = "", None, "Correct"
            if did_buzz:
                answer = self.get_user_input()
                is_correct, match_type = self.grade(answer, correct_answer, question)
            else:
                is_correct, match_type = False, "wrong"

            if is_correct:
                self.score += 1
                if match_type == "exact":
                    self.set_status("CORRECT!", LAUREL)
                else:
                    self.set_status(f"CORRECT! Official answer: {correct_answer}", LAUREL)
            else:
                category = self.question_categories[idx - 1]
                self.category_wrong_counts[category] += 1
                outcome = "Wrong" if did_buzz else "No buzz"
                if did_buzz and self.allow_retry:
                    self.set_status("INCORRECT - you get a second chance!", CRIMSON)
                    self.draw_screen()
                    self.pause(1500)
                    self.read_question(question, full_read=True)
                    answer2 = self.get_user_input(
                        "Second attempt", "SECOND ATTEMPT - not scored", BRONZE)
                    is_correct_2, _ = self.grade(answer2, correct_answer, question)
                    if is_correct_2:
                        outcome = "Second try"
                        self.second_try_correct_count += 1
                        self.set_status(
                            f"Correct on the second try (not scored). Answer: {correct_answer}",
                            BRONZE)
                    else:
                        self.wrong_count += 1
                        self.set_status(f"Wrong again. Answer: {correct_answer}", CRIMSON)
                elif did_buzz:
                    self.wrong_count += 1
                    self.set_status("INCORRECT", CRIMSON)
                    self.draw_screen()
                    self.pause(1000)
                    self.read_question(question, full_read=True)
                    self.set_status(f"The correct answer was: {correct_answer}", CRIMSON)
                else:
                    self.wrong_count += 1
                    self.set_status(f"Time's up - counted wrong. Answer: {correct_answer}", CRIMSON)

            self.report.append({"question": question, "correct": correct_answer,
                                "answer": answer, "answer2": answer2, "outcome": outcome})
            self.answered += 1
            self.draw_screen()
            self.pause(2000)

            if idx < self.total_questions:
                self.set_status("Press SPACE for the next question", INK)
                self.wait_for_space()

        percentage = self.score / self.total_questions * 100
        return self.show_results(percentage)

    def show_results(self, percentage):
        while True:
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    self.quit_app()
                if event.type == pygame.KEYDOWN:
                    if event.key in (pygame.K_SPACE, pygame.K_ESCAPE):
                        return event.key
                    if event.key == pygame.K_r:
                        self.show_report()
            self.draw_final_results(percentage)
            self.clock.tick(30)

    # ------------------------------------------------------------------ full report
    OUTCOMES = {"Correct": ("Correct", LAUREL), "Second try": ("Correct on second try", BRONZE),
                "Wrong": ("Wrong", CRIMSON), "No buzz": ("No buzz - time's up", CRIMSON)}

    def build_report_blocks(self):
        font, label_w, x_pad = self.small_font, 150, 18
        inner = 860 - 2 * x_pad
        blocks = []
        for i, e in enumerate(self.report, 1):
            title, color = self.OUTCOMES[e["outcome"]]
            first_ok = e["outcome"] == "Correct"
            rows = [("Question", e["question"], INK),
                    ("Your answer", e["answer"] or "(no answer)", LAUREL if first_ok else CRIMSON)]
            if e["answer2"] is not None:
                rows.append(("Second try", e["answer2"] or "(no answer)",
                             LAUREL if e["outcome"] == "Second try" else CRIMSON))
            rows.append(("Correct answer", e["correct"], INK))
            height = 14 + self.text_font.get_linesize() + 6
            sized = []
            for label, text, col in rows:
                h = len(self.wrap_text(text, font, inner - label_w)) * font.get_linesize()
                sized.append((label, text, col, h))
                height += h + 4
            blocks.append((height + 10, f"{to_roman(i)}.  {title}", color, sized))
        return blocks

    def draw_report_block(self, block, x, y):
        height, title, color, rows = block
        rect = pygame.Rect(x, y, 860, height)
        pygame.draw.rect(self.screen, MARBLE, rect)
        pygame.draw.rect(self.screen, GOLD, rect, 2)
        pygame.draw.rect(self.screen, color, (x, y, 8, height))
        cy = y + 14
        cy += self.draw_text(title, self.text_font, color, x + 26, cy) + 6
        for label, text, col, h in rows:
            self.draw_text(label + ":", self.small_font, BRONZE, x + 26, cy)
            self.draw_text(text, self.small_font, col, x + 26 + 150, cy, max_width=860 - 36 - 150)
            cy += h + 4

    def show_report(self):
        blocks = self.build_report_blocks()
        gap, top, bottom = 10, 150, 640
        view_h = bottom - top
        total = sum(b[0] + gap for b in blocks)
        max_scroll = max(0, total - view_h)
        scroll = 0
        correct = sum(1 for e in self.report if e["outcome"] == "Correct")
        while True:
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    self.quit_app()
                elif event.type == pygame.MOUSEWHEEL:
                    scroll -= event.y * 60
                elif event.type == pygame.KEYDOWN:
                    k = event.key
                    if k in (pygame.K_ESCAPE, pygame.K_r, pygame.K_BACKSPACE):
                        return
                    elif k == pygame.K_DOWN:
                        scroll += 50
                    elif k == pygame.K_UP:
                        scroll -= 50
                    elif k == pygame.K_PAGEDOWN:
                        scroll += view_h - 40
                    elif k == pygame.K_PAGEUP:
                        scroll -= view_h - 40
                    elif k == pygame.K_HOME:
                        scroll = 0
                    elif k == pygame.K_END:
                        scroll = max_scroll
            scroll = max(0, min(max_scroll, scroll))

            self.draw_background()
            self.draw_centered(f"FULL REPORT  -  {correct} of {len(self.report)} correct on the first try",
                               self.text_font, PURPLE, 126)
            self.screen.set_clip(pygame.Rect(0, top, self.width, view_h))
            y = top - scroll
            for block in blocks:
                if y + block[0] >= top and y <= bottom:
                    self.draw_report_block(block, 70, y)
                y += block[0] + gap
            self.screen.set_clip(None)
            if max_scroll:
                track = pygame.Rect(self.width - 24, top, 6, view_h)
                pygame.draw.rect(self.screen, SAND, track)
                thumb_h = max(30, int(view_h * view_h / total))
                thumb_y = top + int((view_h - thumb_h) * scroll / max_scroll)
                pygame.draw.rect(self.screen, PURPLE, (track.x, thumb_y, 6, thumb_h))
            self.draw_centered("Scroll with the mouse wheel or arrow keys  |  ESC to go back",
                               self.small_font, STONE, 658)
            pygame.display.flip()
            self.clock.tick(60)

    def draw_final_results(self, percentage):
        self.draw_background()
        w = self.width
        self.draw_centered("QUIZ COMPLETE", self.heading_font, PURPLE, 132)
        if percentage >= 90:
            tagline = "Veni, vidi, vici."
        elif percentage >= 70:
            tagline = "A worthy legionary."
        elif percentage >= 50:
            tagline = "The legion holds the line."
        else:
            tagline = "Back to the training ground."
        self.draw_centered(tagline, self.small_font, BRONZE, 166)

        score_color = LAUREL if percentage >= 70 else BRONZE if percentage >= 50 else CRIMSON
        self.draw_centered(
            f"Final Score: {self.score}/{self.total_questions} ({percentage:.1f}%)",
            self.text_font, score_color, 205)
        self.draw_centered(
            f"Correct: {self.score}   |   Correct on 2nd try: {self.second_try_correct_count}"
            f"   |   Wrong: {self.wrong_count}",
            self.small_font, INK, 240, max_width=w - 80)

        if self.buzz_times:
            buzz = (f"Buzz times ({len(self.buzz_times)}, from question start): "
                    f"fastest {min(self.buzz_times):.2f}s | slowest {max(self.buzz_times):.2f}s | "
                    f"average {sum(self.buzz_times) / len(self.buzz_times):.2f}s")
        else:
            buzz = "No buzzes recorded."
        self.draw_centered(buzz, self.small_font, INK, 272, max_width=w - 80)

        categorised = set(self.question_categories) != {"Uncategorized"}
        if not categorised:
            self.draw_centered("Set GEMINI_API_KEY to see a breakdown by category.",
                               self.small_font, STONE, 330)
        else:
            missed = sorted(((c, n) for c, n in self.category_wrong_counts.items() if n > 0),
                            key=lambda item: (-item[1], item[0].casefold()))
            if not missed:
                self.draw_centered("No wrong answers - no weakest category!",
                                   self.text_font, LAUREL, 330)
            else:
                top = missed[0][1]
                worst = ", ".join(c for c, n in missed if n == top)
                self.draw_centered(f"Weakest category: {worst} ({top} wrong)",
                                   self.text_font, BRONZE, 322, max_width=w - 80)
                self.draw_centered("Missed on first attempt, by category:",
                                   self.small_font, INK, 360)
                rows_cap, max_cols = 10, 3
                shown = missed[:rows_cap * max_cols]
                cols = max(1, -(-len(shown) // rows_cap))
                rows = -(-len(shown) // cols)
                col_w = (w - 80) // cols
                for i, (cat, count) in enumerate(shown):
                    col, row = divmod(i, rows)
                    text = self.ellipsize(f"{cat}: {count}", self.small_font, col_w - 20)
                    self.draw_text(text, self.small_font, INK,
                                   40 + col * col_w, 384 + row * 24, max_width=col_w)
                if len(missed) > len(shown):
                    self.draw_centered(f"...and {len(missed) - len(shown)} more",
                                       self.small_font, STONE, 636)

        self.draw_centered("R: full report   |   SPACE: new question count   |   ESC: new file",
                           self.small_font, PURPLE, 658, max_width=w - 80)
        pygame.display.flip()

    # ------------------------------------------------------------------ setup-screen events
    def on_file_input_event(self, event, rects):
        browse, submit = rects
        if event.type == pygame.KEYDOWN:
            if event.key == pygame.K_ESCAPE:
                self.quit_app()
            elif event.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
                if self.file_input_text.strip():
                    self.file_error = self.try_set_file(self.file_input_text)
            elif event.key == pygame.K_BACKSPACE:
                self.file_input_text = self.file_input_text[:-1]
                self.file_error = ""
            elif event.key == pygame.K_v and (pygame.key.get_mods() & (pygame.KMOD_CTRL | pygame.KMOD_META)):
                pasted = " ".join(self.get_clipboard_text().split())
                if pasted:
                    self.file_input_text += pasted
                    self.file_error = ""
            elif event.unicode and event.unicode.isprintable():
                self.file_input_text += event.unicode
                self.file_error = ""
        elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
            if browse.collidepoint(event.pos):
                path = self.select_csv_file()
                if path:
                    self.file_error = self.try_set_file(path)
            elif submit and submit.collidepoint(event.pos):
                self.file_error = self.try_set_file(self.file_input_text)
        elif event.type == pygame.DROPFILE:
            self.file_error = self.try_set_file(event.file)

    def confirm_column(self):
        self.question_column = self.selected_column
        if self.load_questions():
            self.question_count_text = ""
            self.question_count_error = ""
            self.screen_state = "question_count_selection"

    def on_column_event(self, event, rects):
        r1, r2, cont = rects
        if event.type == pygame.KEYDOWN:
            if event.key == pygame.K_ESCAPE:
                self.screen_state = "file_input"
            elif event.key in (pygame.K_1, pygame.K_KP1):
                self.selected_column = 1
            elif event.key in (pygame.K_2, pygame.K_KP2):
                self.selected_column = 2
            elif event.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
                self.confirm_column()
        elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
            if r1.collidepoint(event.pos):
                self.selected_column = 1
            elif r2.collidepoint(event.pos):
                self.selected_column = 2
            elif cont.collidepoint(event.pos):
                self.confirm_column()

    def confirm_count(self):
        if self.apply_question_count():
            self.screen_state = "retry_selection"

    def on_count_event(self, event, cont):
        if event.type == pygame.KEYDOWN:
            if event.key == pygame.K_ESCAPE:
                self.screen_state = "column_selection"
            elif event.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
                self.confirm_count()
            elif event.key == pygame.K_BACKSPACE:
                self.question_count_text = self.question_count_text[:-1]
                self.question_count_error = ""
            elif (event.unicode.isdecimal()
                  and len(self.question_count_text) < len(str(len(self.available_questions)))):
                self.question_count_text += event.unicode
                self.question_count_error = ""
        elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
            if cont.collidepoint(event.pos):
                self.confirm_count()

    def start_quiz(self):
        self.screen_state = "quiz"
        key = self.run_quiz()
        if key == pygame.K_SPACE:
            self.question_count_text = ""
            self.question_count_error = ""
            self.screen_state = "question_count_selection"
        else:
            self.csv_file = None
            self.file_input_text = ""
            self.file_error = ""
            self.questions = []
            self.available_questions = []
            self.screen_state = "file_input"

    def on_retry_event(self, event, rects):
        yes, no, start = rects
        if event.type == pygame.KEYDOWN:
            if event.key == pygame.K_ESCAPE:
                self.screen_state = "question_count_selection"
            elif event.key == pygame.K_y:
                self.allow_retry = True
            elif event.key == pygame.K_n:
                self.allow_retry = False
            elif event.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
                self.start_quiz()
        elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
            if yes.collidepoint(event.pos):
                self.allow_retry = True
            elif no.collidepoint(event.pos):
                self.allow_retry = False
            elif start.collidepoint(event.pos):
                self.start_quiz()

    # ------------------------------------------------------------------ main loop
    def run(self):
        draw = {
            "file_input": self.draw_file_input_screen,
            "column_selection": self.draw_column_selection_screen,
            "question_count_selection": self.draw_question_count_selection_screen,
            "retry_selection": self.draw_retry_selection_screen,
        }
        handle = {
            "file_input": self.on_file_input_event,
            "column_selection": self.on_column_event,
            "question_count_selection": self.on_count_event,
            "retry_selection": self.on_retry_event,
        }
        while True:
            state = self.screen_state
            rects = draw[state]()
            pygame.display.flip()
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    self.quit_app()
                handle[state](event, rects)
                if self.screen_state != state:
                    break
            self.clock.tick(60)


if __name__ == "__main__":
    print("QUIZ BUZZER SYSTEM")
    print("==================")
    QuizBuzzer().run()