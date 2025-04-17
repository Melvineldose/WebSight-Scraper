# Web Scraper with Streamlit UI
# A professional web scraping tool that captures website screenshots and content

import streamlit as st
import requests
from bs4 import BeautifulSoup
from urllib.parse import urljoin, urlparse
import time
import logging
from datetime import datetime
import os
import random
import hashlib
from typing import Set, Dict, List, Optional
import concurrent.futures
from requests.adapters import HTTPAdapter
from requests.packages.urllib3.util.retry import Retry
from reportlab.lib.pagesizes import A4, landscape, letter
from reportlab.pdfgen import canvas
from reportlab.lib import colors
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Image, PageBreak, Table, TableStyle
from reportlab.lib.units import inch
from PIL import Image as PILImage
from io import BytesIO
import re
from dataclasses import dataclass
from pathlib import Path
from collections import deque
import base64
from selenium import webdriver
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
from webdriver_manager.chrome import ChromeDriverManager
import uuid
import tempfile
import threading

# Configure logging
logging.basicConfig(level=logging.INFO, 
                    format='%(asctime)s - %(levelname)s - %(message)s')

# Create static folder if not exists (for PDFs)
os.makedirs('static', exist_ok=True)

# Define the PageContent dataclass
@dataclass
class PageContent:
    url: str
    title: str
    content: List[Dict]
    level: int  # For hierarchy in PDF
    screenshot_path: Optional[str] = None
    css_styles: Optional[Dict] = None
    dom_structure: Optional[Dict] = None

class UnifiedWebsiteScraper:
    def __init__(
        self,
        start_url: str,
        output_dir: str = "static",
        max_pages: int = 5,
        concurrent_requests: int = 5,
        delay_range: tuple = (1, 3),
        capture_screenshots: bool = True,
        capture_css: bool = False,  
        capture_dom: bool = False,  
        headless: bool = True,
        progress_callback=None  # Add a callback function for progress updates
    ):
        self.start_url = start_url
        self.base_domain = urlparse(start_url).netloc
        self.scheme = urlparse(start_url).scheme
        self.output_dir = output_dir
        self.max_pages = min(max_pages, 10)  # Ensure max_pages doesn't exceed 10
        self.concurrent_requests = concurrent_requests
        self.delay_range = delay_range
        self.capture_screenshots = capture_screenshots
        self.capture_css = capture_css
        self.capture_dom = capture_dom
        self.headless = headless
        self.progress_callback = progress_callback
        
        # Initialize tracking
        self.visited_urls: Set[str] = set()
        self.failed_urls: Set[str] = set()
        self.queue: deque = deque([(start_url, 0)])  # (url, level)
        self.content_store: List[PageContent] = []
        
        # Setup
        self._setup_directories()
        self.session = self._setup_session()
        
        # Setup Selenium if needed
        if self.capture_screenshots:
            try:
                self.driver = self._setup_selenium()
                if self.driver is None:
                    logging.warning("Selenium initialization failed. Screenshots will be disabled.")
                    self.capture_screenshots = False
            except Exception as e:
                logging.error(f"Failed to initialize Selenium: {str(e)}. Screenshots will be disabled.")
                self.capture_screenshots = False

    def _setup_directories(self):
        """Create only necessary directory for PDFs"""
        os.makedirs(self.output_dir, exist_ok=True)

    def _setup_session(self) -> requests.Session:
        """Set up requests session with retry strategy"""
        session = requests.Session()
        retry_strategy = Retry(
            total=3,
            backoff_factor=0.5,
            status_forcelist=[500, 502, 503, 504]
        )
        adapter = HTTPAdapter(max_retries=retry_strategy)
        session.mount("http://", adapter)
        session.mount("https://", adapter)
        return session

    def _setup_selenium(self) -> webdriver.Chrome:
        """Set up Selenium WebDriver with improved error handling and reconnection capability"""
        chrome_options = Options()
        if self.headless:
            chrome_options.add_argument("--headless")
        chrome_options.add_argument("--no-sandbox")
        chrome_options.add_argument("--disable-dev-shm-usage")
        chrome_options.add_argument("--disable-gpu")
        chrome_options.add_argument("--window-size=1280,800")  # Smaller window to reduce memory usage
        
        # Add options to handle connection issues
        chrome_options.add_argument("--dns-prefetch-disable")
        chrome_options.add_argument("--disable-extensions")
        chrome_options.add_argument("--disable-infobars")
        
        # Add page load timeout to prevent hanging
        chrome_options.page_load_strategy = 'eager'  # Don't wait for all resources to load
        
        max_attempts = 3
        for attempt in range(max_attempts):
            try:
                # Create a fallback for the chromedriver
                try:
                    # First try with WebDriverManager (with specific Chrome version)
                    service = Service(ChromeDriverManager(version="stable").install())
                    driver = webdriver.Chrome(service=service, options=chrome_options)
                except Exception as wdm_error:
                    logging.warning(f"WebDriverManager failed: {str(wdm_error)}. Trying direct ChromeDriver...")
                    # Fallback to system ChromeDriver if available
                    try:
                        service = Service("chromedriver")
                        driver = webdriver.Chrome(service=service, options=chrome_options)
                    except Exception as direct_error:
                        # Try with a simpler approach using ChromeOptions directly
                        logging.warning(f"Direct ChromeDriver failed: {str(direct_error)}. Trying simpler approach...")
                        from selenium.webdriver.chrome.service import Service as ChromeService
                        driver = webdriver.Chrome(options=chrome_options)
                
                driver.set_page_load_timeout(30)  # Set page load timeout
                driver.set_script_timeout(30)     # Set script execution timeout
                return driver
            except Exception as e:
                if attempt < max_attempts - 1:
                    logging.warning(f"Failed to initialize Selenium WebDriver (attempt {attempt+1}/{max_attempts}): {str(e)}")
                    time.sleep(2)  # Wait before retry
                else:
                    logging.error(f"Failed to initialize Selenium WebDriver after {max_attempts} attempts: {str(e)}")
                    # Instead of raising an exception, return None and let the caller handle it
                    return None

    def _use_selenium_with_retry(self, url, operation_func, max_retries=3):
        """Helper method to handle Selenium operations with retry logic"""
        retry_count = 0
        while retry_count < max_retries:
            try:
                # Navigate to the URL with timeout protection
                try:
                    self.driver.get(url)
                    # Wait for page to load
                    time.sleep(3)
                    return operation_func()
                except Exception as e:
                    if "timeout" in str(e).lower() or "connection" in str(e).lower():
                        raise  # Re-raise for connection errors to trigger retry
                    logging.warning(f"Non-connection error in Selenium operation: {str(e)}")
                    return None
            except Exception as e:
                retry_count += 1
                logging.warning(f"Selenium operation failed (attempt {retry_count}/{max_retries}): {str(e)}")
                
                if retry_count >= max_retries:
                    logging.error(f"Selenium operation failed after {max_retries} attempts")
                    return None
                
                # Check if driver is still responsive
                try:
                    # Simple command to check if driver is alive
                    self.driver.title
                except:
                    # Driver crashed, restart it
                    logging.warning("Selenium WebDriver crashed, restarting...")
                    try:
                        self.driver.quit()
                    except:
                        pass  # Already crashed
                    self.driver = self._setup_selenium()
                
                time.sleep(2)  # Wait before retry

    def _normalize_url(self, url: str) -> str:
        """Normalize URL by handling protocol-relative URLs"""
        if url.startswith('//'):
            return f"{self.scheme}:{url}"
        return url

    def _extract_content(self, soup: BeautifulSoup, url: str) -> List[Dict]:
        """Extract content blocks from page"""
        content_blocks = []
        
        main_content = soup.find(['article', 'main']) or soup.find('div', class_=re.compile(r'content|post|article|entry'))
        if not main_content:
            main_content = soup
        
        for element in main_content.find_all(['p', 'h1', 'h2', 'h3', 'h4', 'blockquote', 'div', 'span', 'ul', 'ol', 'li', 'table']):
            if element.name in ['ul', 'ol']:
                list_items = []
                for li in element.find_all('li', recursive=False):
                    text = li.get_text(strip=True)
                    if text:
                        list_items.append(text)
                
                if list_items:
                    content_blocks.append({
                        'type': 'list',
                        'items': list_items,
                        'list_type': 'ordered' if element.name == 'ol' else 'unordered',
                        'style': element.get('style', ''),
                        'class': element.get('class', '')
                    })
            elif element.name == 'table':
                rows = []
                for tr in element.find_all('tr', recursive=False):
                    row = []
                    for td in tr.find_all(['td', 'th']):
                        cell_text = td.get_text(strip=True)
                        cell_type = 'header' if td.name == 'th' else 'cell'
                        row.append({
                            'text': cell_text,
                            'type': cell_type,
                            'colspan': int(td.get('colspan', 1)),
                            'rowspan': int(td.get('rowspan', 1))
                        })
                    if row:
                        rows.append(row)
                
                if rows:
                    content_blocks.append({
                        'type': 'table',
                        'rows': rows,
                        'style': element.get('style', ''),
                        'class': element.get('class', '')
                    })
            else:
                # Extract text content
                text = element.get_text(strip=True)
                if text and element.name not in ['li']:  # Skip li as they're handled in list processing
                    content_blocks.append({
                        'type': 'text',
                        'content': text,
                        'tag': element.name,
                        'style': element.get('style', ''),
                        'class': element.get('class', '')
                    })
        
        return content_blocks

    def _extract_links(self, soup: BeautifulSoup, base_url: str) -> List[str]:
        """Extract and normalize links"""
        links = []
        for a in soup.find_all('a', href=True):
            href = a['href']
            href = self._normalize_url(href)
            absolute_url = urljoin(base_url, href)
            if urlparse(absolute_url).netloc == self.base_domain:
                links.append(absolute_url)
        return list(set(links))

    def _capture_screenshot(self, url: str) -> Optional[str]:
        """Capture full page screenshot using Selenium with retry logic"""
        url_hash = hashlib.md5(url.encode()).hexdigest()
        screenshot_path = f"{self.output_dir}/temp_screenshot_{url_hash}.png"
        
        def take_screenshot():
            # Get the height of the page (limited to prevent excessive size)
            height = min(10000, self.driver.execute_script(
                "return Math.max(document.body.scrollHeight, document.documentElement.scrollHeight);"
            ))
            
            # Set window size to capture most of the page (with reasonable limit)
            self.driver.set_window_size(1280, height)
            
            # Take screenshot
            self.driver.save_screenshot(screenshot_path)
            return screenshot_path
        
        return self._use_selenium_with_retry(url, take_screenshot)

    def _fetch_page(self, url: str, level: int) -> Optional[PageContent]:
        """Fetch and process a single page"""
        try:
            time.sleep(random.uniform(*self.delay_range))
            
            response = self.session.get(url, timeout=10)
            response.raise_for_status()
            
            soup = BeautifulSoup(response.text, 'html.parser')
            
            title = soup.title.string if soup.title else url
            content_blocks = self._extract_content(soup, url)
            
            # Only add new URLs to queue if we haven't reached our target yet
            remaining_slots = self.max_pages - len(self.visited_urls) - len(self.queue)
            if remaining_slots > 0:
                new_links = self._extract_links(soup, url)
                # Sort links to prioritize shorter paths (usually more important pages)
                new_links.sort(key=lambda x: len(urlparse(x).path.split('/')))
                # Only add a limited number of new links
                added_count = 0
                for link in new_links:
                    if link not in self.visited_urls and link not in [u for u, _ in self.queue]:
                        self.queue.append((link, level + 1))
                        added_count += 1
                        if added_count >= remaining_slots:
                            break
            
            # Capture screenshot if enabled
            screenshot_path = None
            if self.capture_screenshots:
                screenshot_path = self._capture_screenshot(url)
            
            return PageContent(
                url=url,
                title=title,
                content=content_blocks,
                level=level,
                screenshot_path=screenshot_path,
                css_styles=None,  # Not capturing CSS
                dom_structure=None  # Not capturing DOM
            )
            
        except Exception as e:
            logging.error(f"Error fetching {url}: {str(e)}")
            self.failed_urls.add(url)
            return None

    def _create_screenshots_only_pdf(self) -> str:
        """Create a PDF containing only screenshots of the website UI without any blank spaces or pages"""
        try:
            import math  # Import math module for ceil function
            
            # Ensure we only include max_pages screenshots in the PDF
            if len(self.content_store) > self.max_pages:
                logging.warning(f"Limiting PDF content to {self.max_pages} pages (had {len(self.content_store)} pages)")
                self.content_store = self.content_store[:self.max_pages]
            
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            filename = f"website_screenshots_{timestamp}.pdf"
            pdf_path = f"{self.output_dir}/{filename}"
            
            # Filter valid screenshots and process them first
            valid_screenshots = []
            screenshot_count = 0
            
            for page in self.content_store:
                if screenshot_count >= self.max_pages:
                    break
                    
                if page.screenshot_path and os.path.exists(page.screenshot_path):
                    try:
                        with PILImage.open(page.screenshot_path) as pil_img:
                            if pil_img.mode not in ('RGB', 'L'):
                                pil_img = pil_img.convert('RGB')
                            # Only include images with valid dimensions
                            width, height = pil_img.size
                            if width > 0 and height > 0:
                                # Create a clean copy of the image without any transparency
                                temp_path = f"{self.output_dir}/temp_clean_{os.path.basename(page.screenshot_path)}.jpg"
                                pil_img.save(temp_path, 'JPEG', quality=95)
                                valid_screenshots.append({
                                    'page': page,
                                    'width': width,
                                    'height': height,
                                    'clean_path': temp_path
                                })
                                screenshot_count += 1
                    except Exception as e:
                        logging.warning(f"Could not process screenshot for {page.url}: {str(e)}")
            
            if not valid_screenshots:
                # Handle case with no valid screenshots
                # Use A4 for the error message
                c = canvas.Canvas(pdf_path, pagesize=A4)
                c.setFont("Helvetica", 12)
                c.drawString(100, 500, "No valid screenshots were captured.")
                c.save()
                return filename
                
            # Determine best page size based on screenshot dimensions
            # Use the most common width to avoid outliers
            width_counts = {}
            for shot in valid_screenshots:
                width = shot['width']
                width_counts[width] = width_counts.get(width, 0) + 1
            
            # Get the most common width
            most_common_width = max(width_counts.items(), key=lambda x: x[1])[0]
            
            # Use a custom page size that exactly matches the screenshots
            # Add very minimal padding (2px) to avoid cutting off content
            page_width = most_common_width + 4
            
            # Create a new PDF with precise size and no margins
            c = canvas.Canvas(pdf_path, pagesize=(page_width, 800))  # Height will be adjusted per page
            
            # Standard font for titles
            c.setFont("Helvetica", 10)
            
            # Limit the PDF to max_pages physical pages
            total_pdf_pages = 0
            max_pdf_pages = self.max_pages * 2  # Allow up to 2 physical PDF pages per URL (for tall screenshots)
            
            # Process each valid screenshot
            for idx, shot in enumerate(valid_screenshots):
                page = shot['page']
                width = shot['width']
                height = shot['height']
                img_path = shot['clean_path']
                
                # Normalize title
                title = page.title if page.title else f"Page: {page.url}"
                
                # For very tall screenshots, split them but limit total pages
                max_height_per_page = 800  # Maximum reasonable height
                
                if height <= max_height_per_page:
                    # Single page case
                    if total_pdf_pages >= max_pdf_pages:
                        logging.warning(f"Reached maximum PDF pages limit ({max_pdf_pages}). Stopping PDF generation.")
                        break
                        
                    # Set the exact page size needed for this image
                    c.setPageSize((page_width, height + 20))  # 20px extra for the title
                    
                    # Draw the title at the top
                    c.drawString(10, height + 5, title)
                    
                    # Draw the image - centered if narrower than page
                    x_offset = (page_width - width) / 2 if width < page_width else 0
                    c.drawImage(img_path, x_offset, 0, width=width, height=height)
                    
                    # End this page
                    c.showPage()
                    total_pdf_pages += 1
                else:
                    # Split into multiple pages, but limit the total
                    pieces = min(math.ceil(height / max_height_per_page), 2)  # Limit to 2 pieces per screenshot
                    
                    for i in range(pieces):
                        if total_pdf_pages >= max_pdf_pages:
                            logging.warning(f"Reached maximum PDF pages limit ({max_pdf_pages}). Stopping PDF generation.")
                            break
                            
                        # Calculate the slice of the image for this page
                        y_start = i * max_height_per_page
                        y_end = min((i + 1) * max_height_per_page, height)
                        slice_height = y_end - y_start
                        
                        # Create temporary cropped image
                        with PILImage.open(img_path) as full_img:
                            slice_img = full_img.crop((0, y_start, width, y_end))
                            slice_path = f"{self.output_dir}/temp_slice_{i}_{os.path.basename(img_path)}"
                            slice_img.save(slice_path, 'JPEG', quality=95)
                        
                        # Set exact page size for this slice
                        c.setPageSize((page_width, slice_height + 20))  # 20px for title
                        
                        # Draw the title with continuation indicator
                        page_title = f"{title} (part {i+1}/{pieces})" if pieces > 1 else title
                        c.drawString(10, slice_height + 5, page_title)
                        
                        # Draw the slice - centered if narrower than page
                        x_offset = (page_width - width) / 2 if width < page_width else 0
                        c.drawImage(slice_path, x_offset, 0, width=width, height=slice_height)
                        
                        # End this page
                        c.showPage()
                        total_pdf_pages += 1
                        
                    # If we broke out of the loop due to page limit, also break out of the outer loop
                    if total_pdf_pages >= max_pdf_pages:
                        break
            
            # Save the PDF (without adding summary page)
            c.save()
            
            # Clean up temporary files
            self._cleanup_temp_files()
            
            return filename
            
        except Exception as e:
            import traceback
            error_details = traceback.format_exc()
            logging.error(f"Error creating screenshots PDF: {str(e)}\n{error_details}")
            
            # Try to create a simple error PDF
            try:
                c = canvas.Canvas(pdf_path, pagesize=A4)
                c.setFont("Helvetica", 12)
                c.drawString(100, 500, f"Error creating PDF: {str(e)}")
                c.drawString(100, 480, f"Content was scraped from {len(self.content_store)} pages")
                c.save()
                return filename
            except:
                return None
    
    def _cleanup_temp_files(self):
        """Clean up temporary files created during processing"""
        try:
            for file_path in os.listdir(self.output_dir):
                if file_path.startswith('temp_'):
                    try:
                        os.remove(os.path.join(self.output_dir, file_path))
                    except Exception as e:
                        logging.warning(f"Failed to delete temporary file {file_path}: {str(e)}")
        except Exception as e:
            logging.error(f"Error cleaning up temporary files: {str(e)}")

    def scrape_website(self):
        """Main method to scrape website and create PDF with screenshots only"""
        logging.info(f"Starting scrape of {self.start_url}")
        
        # Check if Selenium initialized properly
        if hasattr(self, 'driver') and self.driver is None:
            logging.warning("Selenium WebDriver initialization failed. Continuing without screenshots.")
            self.capture_screenshots = False
        
        selenium_crash_count = 0
        max_selenium_crashes = 3
        
        with concurrent.futures.ThreadPoolExecutor(max_workers=self.concurrent_requests) as executor:
            # Continue until we've either processed the max number of pages
            # or there are no more pages to process
            while self.queue and len(self.visited_urls) < self.max_pages:
                # Process pages in small batches to maintain control over the number of pages
                current_batch = []
                # Only take enough URLs to stay within max_pages limit
                remaining_pages = max(0, self.max_pages - len(self.visited_urls))
                batch_size = min(self.concurrent_requests, remaining_pages, len(self.queue))
                
                for _ in range(batch_size):
                    if self.queue:
                        url, level = self.queue.popleft()
                        if url not in self.visited_urls:
                            current_batch.append((url, level))
                
                if not current_batch:
                    continue
                
                future_to_url = {
                    executor.submit(self._fetch_page, url, level): (url, level) 
                    for url, level in current_batch
                }
                
                for future in concurrent.futures.as_completed(future_to_url):
                    url, level = future_to_url[future]
                    self.visited_urls.add(url)
                    
                    try:
                        content = future.result()
                        if content:
                            self.content_store.append(content)
                            logging.info(f"Processed {url} ({len(self.visited_urls)}/{self.max_pages})")
                            
                            # Update progress if callback is provided
                            if self.progress_callback:
                                progress_percent = min(100, int((len(self.visited_urls) / self.max_pages) * 100))
                                self.progress_callback(progress_percent, f"Processed {len(self.visited_urls)}/{self.max_pages} pages")
                                
                    except Exception as e:
                        logging.error(f"Error processing {url}: {str(e)}")
                        self.failed_urls.add(url)
                        
                        # Check if Selenium error and restart if needed
                        if "selenium" in str(e).lower() or "webdriver" in str(e).lower():
                            selenium_crash_count += 1
                            if selenium_crash_count <= max_selenium_crashes and self.capture_screenshots:
                                logging.warning(f"Selenium issue detected. Restarting WebDriver (attempt {selenium_crash_count}/{max_selenium_crashes})")
                                try:
                                    self.driver.quit()
                                except:
                                    pass
                                self.driver = self._setup_selenium()
                                if self.driver is None:
                                    logging.error("Failed to restart Selenium. Continuing without screenshots.")
                                    self.capture_screenshots = False
                                time.sleep(5)  # Allow time for recovery
                            else:
                                logging.error(f"Too many Selenium crashes ({max_selenium_crashes}). Continuing without screenshots.")
                                self.capture_screenshots = False
                    
                    # Check if we've reached the max number of pages
                    if len(self.visited_urls) >= self.max_pages:
                        logging.info(f"Reached max pages limit ({self.max_pages}). Stopping scrape.")
                        break
        
        # Close selenium driver if it was used
        if hasattr(self, 'driver') and self.driver is not None:
            try:
                self.driver.quit()
            except:
                pass
        
        # Strictly limit content store to max_pages
        if len(self.content_store) > self.max_pages:
            logging.warning(f"Limiting content to {self.max_pages} pages (had {len(self.content_store)})")
            self.content_store = self.content_store[:self.max_pages]
        
        # Final progress update
        if self.progress_callback:
            self.progress_callback(100, f"Completed scraping {len(self.visited_urls)} pages")
            
        # Create PDF - fallback to text-only if screenshots are disabled
        if self.capture_screenshots:
            logging.info("Creating screenshots-only PDF...")
            pdf_filename = self._create_screenshots_only_pdf()
        else:
            logging.info("Creating text-only PDF...")
            # Generate a simple PDF with just the website text
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            pdf_filename = f"website_text_{timestamp}.pdf"
            pdf_path = f"{self.output_dir}/{pdf_filename}"
            
            # Create a simple PDF with just text
            try:
                doc = SimpleDocTemplate(
                    pdf_path,
                    pagesize=letter,
                    rightMargin=72,
                    leftMargin=72,
                    topMargin=72,
                    bottomMargin=72
                )
                
                styles = getSampleStyleSheet()
                story = []
                
                # Add a title page
                title_style = styles["Title"]
                story.append(Paragraph(f"Content from {self.start_url}", title_style))
                story.append(Spacer(1, 12))
                story.append(Paragraph(f"Generated on {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}", styles["Normal"]))
                story.append(PageBreak())
                
                # Add content from each page (limited to max_pages)
                for page in self.content_store[:self.max_pages]:
                    # Add page title
                    page_title = page.title if page.title else page.url
                    story.append(Paragraph(page_title, styles["Heading1"]))
                    story.append(Paragraph(f"URL: {page.url}", styles["Italic"]))
                    story.append(Spacer(1, 12))
                    
                    # Add content blocks
                    for block in page.content:
                        if block['type'] == 'text':
                            tag = block.get('tag', 'p')
                            text = block.get('content', '')
                            
                            if tag in ['h1', 'h2', 'h3', 'h4']:
                                style_name = "Heading" + tag[1]
                                story.append(Paragraph(text, styles.get(style_name, styles["Heading2"])))
                            else:
                                story.append(Paragraph(text, styles["Normal"]))
                                
                        elif block['type'] == 'list':
                            items = block.get('items', [])
                            list_type = block.get('list_type', 'unordered')
                            
                            for i, item in enumerate(items):
                                bullet = f"{i+1}." if list_type == 'ordered' else "•"
                                story.append(Paragraph(f"{bullet} {item}", styles["Normal"]))
                                
                        elif block['type'] == 'table':
                            # Process table
                            rows = block.get('rows', [])
                            if rows:
                                table_data = []
                                for row in rows:
                                    table_row = [cell.get('text', '') for cell in row]
                                    table_data.append(table_row)
                                    
                                if table_data:
                                    table = Table(table_data)
                                    table.setStyle(TableStyle([
                                        ('BACKGROUND', (0, 0), (-1, 0), colors.lightgrey),
                                        ('GRID', (0, 0), (-1, -1), 1, colors.black),
                                        ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold')
                                    ]))
                                    story.append(table)
                                    
                    story.append(PageBreak())
                    
                # Build the PDF
                doc.build(story)
                
            except Exception as e:
                logging.error(f"Error creating text-only PDF: {str(e)}")
                # Create a very simple error PDF
                try:
                    c = canvas.Canvas(pdf_path, pagesize=letter)
                    c.setFont("Helvetica", 12)
                    c.drawString(100, 500, f"Error creating PDF: {str(e)}")
                    c.drawString(100, 480, f"Content was scraped from {len(self.content_store)} pages")
                    c.save()
                except:
                    return None
        
        if pdf_filename:
            logging.info(f"PDF created successfully: {self.output_dir}/{pdf_filename}")
        
        # Log summary
        logging.info(f"Scraping complete. Processed {len(self.visited_urls)} pages. "
                    f"Failed URLs: {len(self.failed_urls)}")
        
        return pdf_filename

# Streamlit UI functions
def get_binary_file_downloader_html(bin_file, file_label='File'):
    """Generate a download link for binary files"""
    with open(bin_file, 'rb') as f:
        data = f.read()
    b64 = base64.b64encode(data).decode()
    href = f'<a href="data:application/octet-stream;base64,{b64}" download="{os.path.basename(bin_file)}" class="download-button">Download {file_label}</a>'
    return href

def display_pdf(file_path):
    """Enhanced PDF display function with multiple rendering options"""
    # Read PDF file
    with open(file_path, "rb") as f:
        base64_pdf = base64.b64encode(f.read()).decode('utf-8')
    
    # Primary method - PDF iframe with proper styling and size
    pdf_display = f"""
        <div style="display: flex; justify-content: center; width: 100%;">
            <iframe 
                src="data:application/pdf;base64,{base64_pdf}" 
                width="100%" 
                height="800px" 
                type="application/pdf"
                style="border: 1px solid #ddd; border-radius: 5px;"
                frameborder="0">
            </iframe>
        </div>
        
        <script>
            // Add event listener to detect if iframe load fails
            document.querySelector('iframe').addEventListener('error', function() {{
                this.style.display = 'none';
                document.getElementById('pdf-fallback').style.display = 'block';
            }});
        </script>
        
        <div id="pdf-fallback" style="display: none; text-align: center; padding: 20px; border: 1px solid #ddd; border-radius: 5px;">
            <p>Your browser cannot display the PDF preview.</p>
            <a href="data:application/pdf;base64,{base64_pdf}" download="{os.path.basename(file_path)}" 
               style="display: inline-block; padding: 10px 20px; background: linear-gradient(90deg, #4b6cb7 0%, #182848 100%); color: white; text-decoration: none; border-radius: 5px; font-weight: bold;">
                Download PDF
            </a>
        </div>
    """
    return pdf_display

# Function to extract first page as image
def extract_pdf_first_page(pdf_path):
    """Extract the first page of a PDF as an image for preview"""
    try:
        import fitz  # PyMuPDF
        
        # Open the PDF
        doc = fitz.open(pdf_path)
        # Get first page
        page = doc[0]
        # Render page to an image with higher resolution
        pix = page.get_pixmap(matrix=fitz.Matrix(2, 2))
        
        # Convert to PIL Image
        img_data = pix.tobytes("png")
        img = PILImage.open(BytesIO(img_data))
        
        # Save as temporary PNG
        temp_img_path = f"{os.path.splitext(pdf_path)[0]}_preview.png"
        img.save(temp_img_path)
        
        return temp_img_path
    except Exception as e:
        st.warning(f"Could not generate preview image: {str(e)}")
        return None

# To implement this in your Streamlit app:
def show_pdf_with_fallbacks(pdf_path):
    """Show PDF with multiple fallback options"""
    # Try iframe approach first
    st.markdown(display_pdf(pdf_path), unsafe_allow_html=True)
    
    # Add a separator
    st.markdown("---")
    
    # Alternative: Generate and show thumbnail preview
    with st.expander("Having trouble viewing the PDF? Click here for thumbnail preview"):
        st.info("PDF preview image (first page only):")
        try:
            # Check if PyMuPDF is available
            import fitz
            # Generate thumbnail
            thumbnail_path = extract_pdf_first_page(pdf_path)
            if thumbnail_path:
                st.image(thumbnail_path, caption="First page preview")
        except ImportError:
            st.warning("PDF thumbnail generation requires PyMuPDF library. Using download only option.")
            # Show download button as fallback
            with open(pdf_path, "rb") as f:
                st.download_button(
                    label="📥 Download PDF",
                    data=f,
                    file_name=os.path.basename(pdf_path),
                    mime="application/pdf"
                )

def main():
    # Set page configuration
    st.set_page_config(
        page_title="WebSight Scraper Pro",
        page_icon="🔍",
        layout="wide",
        initial_sidebar_state="expanded"
    )

    # Custom CSS for better styling
    st.markdown("""
        <style>
        .main-header {
            font-size: 2.5rem;
            background: linear-gradient(90deg, #4b6cb7 0%, #182848 100%);
            -webkit-background-clip: text;
            -webkit-text-fill-color: transparent;
            margin-bottom: 1rem;
            text-align: center;
            font-weight: 700;
        }
        .sub-header {
            color: #505050;
            font-size: 1.2rem;
            text-align: center;
            margin-bottom: 2rem;
        }
        .card {
            padding: 20px;
            border-radius: 10px;
            box-shadow: 0 4px 6px rgba(0,0,0,0.1);
            background-color: white;
            margin-bottom: 20px;
        }
        .feature-icon {
            font-size: 24px;
            margin-right: 10px;
        }
        .feature-title {
            font-weight: 600;
            margin-bottom: 5px;
        }
        .feature-desc {
            color: #666;
        }
        .stProgress > div > div > div {
            background-color: #4b6cb7;
        }
        .download-button {
            display: inline-block;
            padding: 10px 20px;
            background: linear-gradient(90deg, #4b6cb7 0%, #182848 100%);
            color: white;
            text-decoration: none;
            border-radius: 5px;
            font-weight: bold;
            text-align: center;
            margin: 10px 0;
        }
        .download-button:hover {
            background: linear-gradient(90deg, #3a5795 0%, #0b1429 100%);
            color: white;
        }
        .footer {
            text-align: center;
            margin-top: 30px;
            color: #888;
            font-size: 0.8rem;
        }
        </style>
    """, unsafe_allow_html=True)

    # Header
    st.markdown('<h1 class="main-header">WebSight Scraper Pro</h1>', unsafe_allow_html=True)
    st.markdown('<p class="sub-header">Capture, visualize, and download website content with ease</p>', unsafe_allow_html=True)

    # Sidebar
    with st.sidebar:
        st.image("https://img.icons8.com/fluency/96/000000/web-scraping.png", width=80)
        st.markdown("## Configuration")
        
        # Features
        st.markdown("### Features")
        st.markdown("✅ Website Screenshots")
        st.markdown("✅ Content Extraction")
        st.markdown("✅ PDF Generation")
        
        # Tips
        st.markdown("### Tips")
        st.markdown("• For best results, use websites with standard layouts")
        st.markdown("• Increase page limit for larger sites")
        st.markdown("• Screenshots require Chrome/Chromium")
        
        # Footer in sidebar
        st.markdown("---")
        st.markdown("Made with ❤️ by WebSight Team")

    # Main layout with tabs
    tab1, tab2, tab3 = st.tabs(["Scrape Website", "Recent PDFs", "About"])
    
    with tab1:
        st.markdown('<div class="card">', unsafe_allow_html=True)
        
        col1, col2 = st.columns([3, 1])
        
        with col1:
            # URL input
            url = st.text_input("Enter Website URL", placeholder="https://example.com")
            
        with col2:
            # Page limit
            max_pages = st.slider("Max Pages", min_value=1, max_value=10, value=5)
        
        # Capture options
        col1, col2 = st.columns(2)
        with col1:
            capture_screenshots = st.checkbox("Capture Screenshots", value=True)
        with col2:
            headless = st.checkbox("Headless Mode (Faster)", value=True)
            
        st.markdown('</div>', unsafe_allow_html=True)
        
        # Scrape button
        if url:
            if st.button("Start Scraping", use_container_width=True):
                if not url.startswith(('http://', 'https://')):
                    url = 'https://' + url
                
                # Setup progress tracking
                progress_bar = st.progress(0)
                status_text = st.empty()
                
                def update_progress(percent, message):
                    progress_bar.progress(percent)
                    status_text.text(message)
                
                try:
                    with st.spinner('Initializing scraper...'):
                        # Create a unique job ID
                        job_id = str(uuid.uuid4())
                        
                        # Initialize scraper with progress callback
                        scraper = UnifiedWebsiteScraper(
                            start_url=url,
                            output_dir="static",
                            max_pages=max_pages,
                            concurrent_requests=3,
                            delay_range=(1, 2),
                            capture_screenshots=capture_screenshots,
                            capture_css=False,
                            capture_dom=False,
                            headless=headless,
                            progress_callback=update_progress
                        )
                    
                    status_text.text("Starting website scraping...")
                    
                    # Start scraping
                    pdf_filename = scraper.scrape_website()
                    
                    if not pdf_filename:
                        st.error("Failed to generate PDF. Please try again.")
                    else:
                        # Success message
                        st.success(f"Successfully scraped {len(scraper.visited_urls)} pages from {url}")
                        
                        # Store in session state for the Recent PDFs tab
                        if 'pdf_files' not in st.session_state:
                            st.session_state.pdf_files = []
                        
                        pdf_info = {
                            'url': url,
                            'filename': pdf_filename,
                            'path': f"static/{pdf_filename}",
                            'timestamp': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                            'pages_scraped': len(scraper.visited_urls)
                        }
                        
                        # Add to the beginning of the list (most recent first)
                        st.session_state.pdf_files.insert(0, pdf_info)
                        
                        # Show PDF result
                        col1, col2 = st.columns([3, 1])
                        
                        with col1:
                            st.subheader("Preview")
                            pdf_display = display_pdf(f"static/{pdf_filename}")
                            st.markdown(pdf_display, unsafe_allow_html=True)
                            
                        with col2:
                            st.subheader("Information")
                            st.markdown(f"**URL:** {url}")
                            st.markdown(f"**Pages Captured:** {len(scraper.visited_urls)}")
                            st.markdown(f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
                            
                            # Download button
                            st.markdown("### Download")
                            download_button = get_binary_file_downloader_html(
                                f"static/{pdf_filename}", 
                                f"PDF Report ({os.path.basename(pdf_filename)})"
                            )
                            st.markdown(download_button, unsafe_allow_html=True)
                            
                except Exception as e:
                    st.error(f"Error during scraping: {str(e)}")
                    logging.error(f"Scraping error: {str(e)}")
                
                # Reset progress bar
                progress_bar.empty()
        else:
            st.info("Enter a website URL to start scraping.")
            
            # Example cards
            st.markdown("### Example Use Cases")
            
            col1, col2, col3 = st.columns(3)
            
            with col1:
                st.markdown("""
                <div class="card">
                    <div class="feature-title">🔍 Research</div>
                    <div class="feature-desc">Capture online articles and research papers in PDF format for later reference.</div>
                </div>
                """, unsafe_allow_html=True)
                
            with col2:
                st.markdown("""
                <div class="card">
                    <div class="feature-title">📊 Competitor Analysis</div>
                    <div class="feature-desc">Save screenshots of competitor websites to analyze design and content.</div>
                </div>
                """, unsafe_allow_html=True)
                
            with col3:
                st.markdown("""
                <div class="card">
                    <div class="feature-title">📚 Documentation</div>
                    <div class="feature-desc">Create PDFs of documentation websites for offline reading.</div>
                </div>
                """, unsafe_allow_html=True)
    
    with tab2:
        st.markdown("### Recently Created PDFs")
        
        if 'pdf_files' not in st.session_state or not st.session_state.pdf_files:
            st.info("No PDFs have been created yet. Use the 'Scrape Website' tab to generate PDFs.")
        else:
            # Display the recent PDFs
            for i, pdf_info in enumerate(st.session_state.pdf_files):
                with st.expander(f"{pdf_info['url']} - {pdf_info['timestamp']}"):
                    col1, col2 = st.columns([3, 1])
                    
                    with col1:
                        # PDF preview
                        pdf_display = display_pdf(pdf_info['path'])
                        st.markdown(pdf_display, unsafe_allow_html=True)
                        
                    with col2:
                        # PDF info and download
                        st.markdown(f"**Pages:** {pdf_info['pages_scraped']}")
                        st.markdown(f"**Created:** {pdf_info['timestamp']}")
                        
                        # Download button
                        download_button = get_binary_file_downloader_html(
                            pdf_info['path'], 
                            f"PDF Report ({os.path.basename(pdf_info['filename'])})"
                        )
                        st.markdown(download_button, unsafe_allow_html=True)
    
    with tab3:
        # About tab
        st.markdown("## About WebSight Scraper Pro")
        
        st.markdown("""
        WebSight Scraper Pro is a powerful tool designed to capture website content and convert it into downloadable PDF format.
        
        ### Key Features
        
        - **Visual Capture:** Take full-page screenshots of websites
        - **Content Extraction:** Extract text, lists, and tables from web pages
        - **PDF Generation:** Create professional PDF reports with website content
        - **Batch Processing:** Capture multiple pages from a website in one go
        
        ### How It Works
        
        1. Enter a website URL and configure options
        2. The scraper navigates through the website, capturing screenshots and content
        3. All captured content is compiled into a downloadable PDF
        4. View and download your PDF reports
        
        ### Technical Details
        
        The application uses:
        - Selenium WebDriver for browser automation and screenshots
        - BeautifulSoup for HTML parsing and content extraction
        - ReportLab for PDF generation
        - Streamlit for the user interface
        
        ### Privacy & Usage
        
        This tool is for personal and research purposes only. Please respect website terms of service and robots.txt when scraping websites.
        """)
        
        # Contact info
        st.markdown("### Feedback & Support")
        st.markdown("For questions or feedback, please contact us at support@websightscraper.com")
        
    # Footer
    st.markdown("""
    <div class="footer">
        WebSight Scraper Pro v1.0 | Copyright © 2025 | All Rights Reserved
    </div>
    """, unsafe_allow_html=True)

if __name__ == "__main__":
    main()